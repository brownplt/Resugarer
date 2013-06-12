(module macros racket
  (provide
   define-macro lookup-macro
   expand unexpand
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
             (tag-macro (Macro 'name (list (MacroCase pc qc) ...))))))]))
  
  (define (tag-macro m)
    (define (wrap-macro n c)
      (match c
        [(MacroCase left right)
         (MacroCase left (tag right (o-macro (Macro-name m) n)))]))
    (match m
      [(Macro name cases)
       (Macro name (map (λ (n) (wrap-macro n (list-ref cases n)))
                        (range (length cases))))]))
  
  
  (define-syntax-rule (define-macro name case ...)
    (hash-set! global-macro-dictionary 'name
               (compile-macro name case ...)))
  
  (define (lookup-macro name)
    (if (hash-has-key? global-macro-dictionary name)
        (hash-ref global-macro-dictionary name)
        #f))
  
  
  ;;; Expanding & Unexpanding Macros ;;;
  
  (struct NotUnexpandable (pattern) #:transparent)
  
  (define (expand-macro m x)
    (match m
      [(Macro name (list))
       (fail "No matching pattern in macro ~a for ~a" name (show-pattern x))]
      [(Macro name (cons (MacroCase p q) cs))
       (let* [[e (attempt-unification (minus x p))]]
         (if (unification-failure? e)
             (expand-macro (Macro name cs) x)
             (substitute e q)))]))
  
  (define (unexpand-macro x origin)
    (match origin
      [(o-macro m n)
       (let* [[c (list-ref (Macro-cases (lookup-macro m)) n)]
              [lhs (MacroCase-left c)]
              [rhs (MacroCase-right c)]]
         (substitute (minus (tag x (o-macro m n)) rhs (o-branch)) lhs))]))
  
  (define (expand e)
    (match e
      [(constant c)       (constant c)]
      [(literal l)        (literal l)]
      [(tag p o)          (tag (expand p) o)]
      [(plist t ps)
       (if (t-macro? t)
           (expand (expand-macro (lookup-macro (t-macro-name t)) e))
           (plist t (map expand ps)))]))
  
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
        [(plist t ps)   (plist t (map rec ps))]
        [(tag p2 o)     (match o
                          [(o-macro m n) (unexpand-macro (rec p2) o)]
                          #;[(o-branch)
                           (match p2
                             ; Fail to unexpand if a macro is tainted
                             [(tag p3 (o-macro m i n))
                              (tag p3 (o-macro m i n))]
                             [p2 (tag (rec p2) o)])]
                          [(o-branch) (tag (rec p2) o)])]))
    (check-unlittered (rec p)))
  
  (define (unexpand p)
    (with-handlers [[(λ (x) (or (NotUnexpandable? x) (CantMatch? x)))
                     (λ (x) #f)]]
      (unchecked-unexpand p)))
)