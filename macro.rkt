(module macros racket
  (provide
   define-macro lookup-macro
   expand-pattern unexpand-pattern
   ; testing:
   unchecked-unexpand
   NotUnexpandable?
   Macro Macro-cases MacroCase expand-macro)
  (require "utility.rkt")
  (require "pattern.rkt")
  
  
  ;;; Defining Macros ;;;
  
  (struct MacroCase (left right) #:transparent)
  (struct Macro (name cases) #:transparent)
  
  (define global-macro-dictionary (make-hash)) ; { macro-name -> macro }
  
  (define-syntax (compile-macro stx)
    (syntax-case stx ()
      [(compile-macro name [(_ p ...) q] ...)
       (with-syntax ([(pc ...) (generate-temporaries #'((p ...) ...))] ; why (p ...)?
                     [(qc ...) (generate-temporaries #'(q ...))])
         #'(let [[pc (sexpr->pattern '(name p ...) #f #f)] ...]
           (let [[qc (sexpr->pattern 'q (set->list (free-vars pc)) #t)] ...]
             (tag-macro (validate-macro (Macro 'name (list (MacroCase pc qc) ...)))))))]))
  
  (define (tag-macro m)
    (define (wrap-macro i c)
      (match c
        [(MacroCase left right)
         (MacroCase left (tag right (o-macro (Macro-name m) i 'gremlin)))]))
    (match m
      [(Macro name cases)
       (Macro name (map (λ (i) (wrap-macro i (list-ref cases i)))
                        (range (length cases))))]))
  
  
  (define-syntax-rule (define-macro name case ...)
    (hash-set! global-macro-dictionary 'name
               (compile-macro name case ...)))
  
  (define (lookup-macro name)
    (if (hash-has-key? global-macro-dictionary name)
        (hash-ref global-macro-dictionary name)
        #f))
  
  
  ;;; Validating Macros ;;;
  
  (define (check-wf-macro m)
    
    (define (check-wf-case c)
      
      (define (union-vars vs)
        (cond [(empty? vs) (set)]
              [(eq? (length vs) 1) (car vs)]
              [else (let [[overlap (set-intersect (car vs) (cadr vs))]]
                      (if (set-empty? overlap)
                          (union-vars (cons (set-union (car vs) (cadr vs))
                                            (cddr vs)))
                          (duplicate-var-failure m (set-first overlap) c)))]))
      
      (define (check-wf-lhs p)
        (match p
          [(pvar v) (set v)]
          [(literal _) (set)]
          [(constant _) (set)]
          [(tag p _) (check-wf-lhs p)]
          [(plist _ ps) (union-vars (map check-wf-lhs ps))]
          [(ellipsis _ ps r qs)
           (let [[fvr (check-wf-lhs r)]]
             (if (set-empty? fvr)
                 (empty-ellipsis-failure m c)
                 (union-vars (append (map check-wf-lhs ps)
                                     (list fvr)
                                     (map check-wf-lhs qs)))))]))
      
      ; TODO: check that each var on the rhs appears under at least as many
      ;       ellipses as it does in the lhs.
      ; TODO: Figure out duplicate rhs variables.
      (define (check-wf-rhs p)
        (match p
          [(pvar v) (set v)]
          [(literal _) (set)]
          [(constant _) (set)]
          [(tag p _) (check-wf-rhs p)]
          [(plist _ ps) (set-unions (map check-wf-rhs ps))]
          [(ellipsis _ ps r qs)
           (let [[fvr (check-wf-rhs r)]]
             (if (set-empty? fvr)
                 (empty-ellipsis-failure m c)
                 (set-unions (append (map check-wf-rhs ps)
                                     (list fvr)
                                     (map check-wf-rhs qs)))))]))

      (begin (check-wf-lhs (MacroCase-left c))
             (check-wf-rhs (MacroCase-right c))))
    
    (for-each check-wf-case (Macro-cases m)))
  
  (define (validate-macro m)
    (define (validate-pair pair)
      (let* [[c1 (car pair)]
             [c2 (cdr pair)]
             [p1 (MacroCase-left c1)]
             [p2 (MacroCase-left c2)]
             [q1 (MacroCase-right c1)]
             [q2 (MacroCase-right c2)]
             [union (attempt-unification (unify p1 p2))]]
        (when (not (unification-failure? union))
          (validation-failure m c1 c2 union))))

    (begin (check-wf-macro m)
           (for-each validate-pair (all-distinct-pairs (Macro-cases m)))
           m))
  
  (define (show-macro-case c)
    (format "[~a => ~a]"
            (show-pattern (MacroCase-left c))
            (show-pattern (MacroCase-right c))))
  
  (define (validation-failure m c1 c2 p)
    (fail "Invalid macro ~a. Cases ~a and ~a overlap on input ~a."
          (Macro-name m) (show-macro-case c1) (show-macro-case c2) (show-pattern p)))
  
  (define (duplicate-var-failure m v c)
    (fail "Invalid macro ~a. Duplicate variable ~a in case ~a."
          (Macro-name m) v (show-macro-case c)))
  
  (define (empty-ellipsis-failure m c)
    (fail "Invaid macro ~a. Variableless ellipsis in case ~a."
          (Macro-name m) (show-macro-case c)))
  
  
  ;;; Expanding & Unexpanding Macros ;;;
  
  (struct NotUnexpandable (pattern) #:transparent)
  
  (define (expand-macro m x)
    (define (insert-orig-env e p)
      (match p
        [(tag p (o-macro m i _))
         (tag p (o-macro m i e))]))
    (match m
      [(Macro name (list))
       (fail "No matching pattern in macro ~a for ~a" name (show-pattern x))]
      [(Macro name (cons (MacroCase p q) cs))
       (let* [[e (attempt-unification (minus x p))]]
         (if (unification-failure? e)
             (expand-macro (Macro name cs) x)
             (insert-orig-env (hash-remove-keys e (free-vars q))
                              (substitute e q))))]
      [#f (fail "Could not expand: ~a" (show-pattern x))]))
  
  (define (unexpand-macro x origin)
    (match origin
      [(o-macro m i q)
       (let* [[c (list-ref (Macro-cases (lookup-macro m)) i)]
              [lhs (MacroCase-left c)]
              [rhs (MacroCase-right c)]]
         (substitute (hash-union q (minus (tag x (o-macro m i q)) rhs (o-branch))) lhs))]))
  
  (define (expand-pattern e)
    (match e
      [(constant c)       (constant c)]
      [(literal l)        (literal l)]
      [(tag p o)          (tag (expand-pattern p) o)]
      [(plist t ps)
       (cond [(t-macro? t)
              (expand-pattern (expand-macro (lookup-macro (t-macro-name t)) e))]
             [(t-apply? t)
              (plist t (map expand-pattern ps))]
             [(t-syntax? t)
              (fail "expand-pattern: extraneous syntax-parens (^)")])]))
  
  (define (unchecked-unexpand p)
    (define (check-unlittered p)
      (match p
        [(constant c)   (constant c)]
        [(literal l)    (literal l)]
        [(plist t ps)   (plist t (map check-unlittered ps))]
        [(tag p o)      (raise (NotUnexpandable (tag p o)))]))
    (define (rec p)
      (match p
        [(constant c)   (constant c)]
        [(literal l)    (literal l)]
        [(plist (t-apply) ps) (plist (t-apply) (map rec ps))]
        [(tag p2 o)     (match o
                          [(o-macro m i q) (unexpand-macro (rec p2) o)]
                          [(o-branch)
                           (match p2
                             ; Fail to unexpand if a macro is tainted
                             #;[(tag p3 (o-macro m n))
                              (tag p3 (o-macro m n))]
                             [p2 (tag (rec p2) o)])]
                          [(o-branch) (tag (rec p2) o)])]
        [_              (raise (NotUnexpandable p))]))
    (check-unlittered (rec p)))
  
  (define (unexpand-pattern p)
    (with-handlers [[(λ (x) (or (NotUnexpandable? x) (CantMatch? x)))
                     (λ (x) #f)]]
      (unchecked-unexpand p)))
)