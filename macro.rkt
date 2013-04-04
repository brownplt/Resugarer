(module macros racket
  (provide
   define-macro lookup-macro is-macro-literal? all-macro-names
   expand unexpand
   ; testing:
   NotUnexpandable? instantiate-macro
   Macro Macro-cases MacroCase expand-macro)
  (require "utility.rkt")
  (require "pattern.rkt")
  
  
  ;;; Defining Macros ;;;
  
  (struct MacroCase (left right) #:transparent)
  (struct Macro (name cases) #:transparent)
  
  (define global-macro-dictionary (make-hash)) ; { macro-name -> macro }
  (define (all-macro-names) (hash-keys global-macro-dictionary))
  
  (define-syntax (compile-macro stx)
    (syntax-case stx ()
      [(compile-macro name (lit ...) (mac ...) [(_ p ...) q] ...)
       (with-syntax ([(pc ...) (generate-temporaries #'((p ...) ...))] ; why (p ...)?
                     [(qc ...) (generate-temporaries #'(q ...))])
         #'(let [[pc (sexpr->pattern '(name p ...)
                                     '(lit ...)
                                     '(name mac ...)
                                     #f
                                     (list))] ...]
           (let [[qc (sexpr->pattern 'q
                                     '(lit ...)
                                     '(name mac ...)
                                     (set->list (free-vars pc))
                                     (list))] ...]
             (add-global-literals! '(name lit ...))
             (Macro 'name (list (MacroCase pc qc) ...)))))]))
  
  (define (instantiate-macro m id)
    (define (instantiate-type t i n)
      (let [[o (o-macro (Macro-name m) i n)]]
        (match t
          [(t-syntax)       (t-syntax)]
          [(t-apply _)      (t-apply (list o))]
          [(t-macro m _)    (t-macro m (list o))])))
    (define (instantiate-pattern p i n)
      (let [[rec (λ (p) (instantiate-pattern p i n))]]
        (match p
          [(pvar _)            p]
          [(literal _)         p]
          [(constant _)        p]
          [(plist t ps)        (plist (instantiate-type t i n) (map rec ps))]
          [(ellipsis t l m r)  (ellipsis (instantiate-type t i n)
                                         (map rec l)
                                         (rec m)
                                         (map rec r))])))
    (define (instantiate-pair i n c)
      (match c
        [(MacroCase left right)
         (MacroCase left
                    (instantiate-pattern right i n))]))
    (match m
      [(Macro name cases)
       (Macro name (map (λ (n) (instantiate-pair id n (list-ref cases n)))
                        (range (length cases))))]))
  
  (define-syntax-rule (define-macro name lits macs case ...)
    (hash-set! global-macro-dictionary 'name
               (compile-macro name lits macs case ...)))
  
  (define (lookup-macro name)
    (if (hash-has-key? global-macro-dictionary name)
        (hash-ref global-macro-dictionary name)
        #f))
  
  
  ;;; Expanding & Unexpanding Macros ;;;
  
  (struct NotUnexpandable ())
    
  (define global-macro-expansion-counter 42)
  
  (define (next-macro-expansion-id)
    (set! global-macro-expansion-counter (+ global-macro-expansion-counter 1))
    global-macro-expansion-counter)
  
  (define (expand-macro m x [id (gensym)])
    (define (expand-instantiated-macro m x id)
      (match m
        [(Macro name (list))
         (error (format "No matching pattern in macro ~a for ~a" name (show-pattern x)))]
        [(Macro name (cons (MacroCase p q) cs))
         (let* [[e (attempt-unification (minus x p))]]
           (if (unification-failure? e)
               (expand-instantiated-macro (Macro name cs) x id)
               (substitute e q)))]))
    (expand-instantiated-macro (instantiate-macro m id) x id))
  
  (define (unexpand-macro x origin)
    (match origin
      [(o-macro m i n)
       (let* [[c (list-ref (Macro-cases (lookup-macro m)) n)]
              [lhs (MacroCase-left c)]
              [rhs (MacroCase-right c)]]
         #|(display (format "Unexpand ~a (~a => ~a)\n"
                          (show-pattern x)
                          (show-pattern lhs)
                          (show-pattern rhs)))|#
         (substitute (minus x rhs origin) lhs))]))
  
  (define (expand e)
    (match e
      [(constant c)       (constant c)]
      [(literal l)        (literal l)]
      [(plist t ps)
       (if (t-macro? t)
           (expand (expand-macro (lookup-macro (t-macro-name t)) e))
           (plist t (map expand ps)))]))
  
  (define (unexpand p)
    (define (get-origins t)
      (match t
        [(t-syntax)      #f] ; impossible?
        [(t-apply o)     o]
        [(t-macro m o)   o])) ; impossible?
    (define (rec p)
      (match p
        [(constant c)   (constant c)]
        [(literal l)    (literal l)]  ; impossible?
        [(plist t ps)   (match (get-origins t)
                          [(cons (o-macro m i n) os)
                           (unexpand (unexpand-macro p (o-macro m i n)))]
                          [_ (plist t (map rec ps))])]))
    (with-handlers [[(λ (x) (or (NotUnexpandable? x) (CantMatch? x)))
                     (λ (x) #f)]]
      (rec p)))
)