(module resugar racket
  (require redex)
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  
  #|
  (define-syntax-rule
    (define-macro-aware-language new-lang old-lang e E)
    (define-extended-language new-lang old-lang
      (e ....
         (tag e any any))
      (E ....
         (tag E any any))))
  
  (define-syntax-rule
    (macro-aware-reduction-relation red lang v E)
    (extend-reduction-relation
     red lang (--> (in-hole E (tag v any_1 any_2))
                   (in-hole E v)
                   "macro-aware/tag-elimination")))
|#
  (define-syntax-rule (user-term t)
    (sexpr->pattern 't (all-macro-literals) (all-macro-names) '() (o-user)))
  
  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)))
  #|
  (define (make-user-term t)
    (match t
      [(? atomic? t) t]
      [(? list? t)   (cons (list 'origin (o-user))
                           (map make-user-term t))]))

  (define-syntax-rule (user-term t)
    (make-user-term 't))
|#

  (define (term->pattern t)
    (match t
      [(? atomic? t)              (constant t)]
      [(cons (list 'origin o) ts) (plist (t-apply o)
                                         (map term->pattern ts))]))

  (define (pattern->term p)
    (match p
      [(constant c)                c]
      [(plist (t-apply o) ps)      (cons (list 'origin o)
                                         (map pattern->term ps))]))
  
  (define (show-term t)
    (match t
      [(? atomic? t)               (show t)]
      [(cons (list 'origin o) ts)  (format "(~a)"
                                           (string-join (map show-term ts) " "))]))
  
  (define (expand-term p) ; pattern -> term
    (pattern->term (expand p)))
  
  (define (unexpand-term t) ; term -> pattern
    (unexpand (term->pattern t)))
  
  (define (macro-aware-step lang red p)
    (display (show-pattern p)) (display "\n")
    (define (catmap f xs) (append* (map f xs)))
    (define (step t) (apply-reduction-relation red t))
    (define (new-step t) (catmap resugar (step t)))
    (define (resugar t)
      (let ((p (unexpand-term t)))
        (if p (list p) (begin (display (format "SKIP ~a\n" (show-term t)))
                              (new-step t)))))
    (new-step (expand-term p)))
  
  (define (macro-aware-eval lang red term)
    ;(display (format "\t~a\n" (show-pattern term)))
    (let ((next-terms (macro-aware-step lang red term)))
      (cons (show-pattern term #t)
            (if (empty? next-terms)
                (list)
                (macro-aware-eval lang red (car next-terms))))))
  
  
  ;;; Testing ;;;
  
  (define-language Mirror
    [e (t e ...)
       (t + e ...)
       (t if0 e e e)
       (t rec x e)
       x
       v]
    [v (t λ x e)
       number]
    [E (t v ... E e ...)
       (t if0 E e e)
       (t + v ... E e ...)
       hole]
    [x variable-not-otherwise-mentioned]
    [t (origin any)])
  
  (define-metafunction Mirror
    swap : x x any -> any
    [(swap x_1 x_2 x_1) x_2]
    [(swap x_1 x_2 x_2) x_1]
    [(swap x_1 x_2 (any_1 ...)) ((swap x_1 x_2 any_1) ...)]
    [(swap x_1 x_2 any_1) any_1])
  
  (define-metafunction Mirror
    subs : x e e -> e
    [(subs x_1 e_1 (λ x_1 e_2))
     (λ x_1 e_2)]
    [(subs x_1 e_1 (λ x_2 e_2))
     ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
                (term (λ x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]
    [(subs x_1 e_1 (rec x_2 e_2))
     ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
                (term (rec x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]
    [(subs x_1 e_1 x_1) e_1]
    [(subs x_1 e_1 x_2) x_2]
    [(subs x_1 e_1 (e_2 ...))
     ((subs x_1 e_1 e_2) ...)]
    [(subs x e number) number]
    [(subs x e (+ e_1 ...)) (+ (subs x e e_1) ...)]
    [(subs x e (if0 e_1 e_2 e_3))
     (if0 (subs x e e_1) (subs x e e_2) (subs x e e_3))])
  
  (define red
    (reduction-relation
     Mirror
     (--> (in-hole E (t if0 0 e_1 e_2))
          (in-hole E e_1)
          "if0_true")
     (--> (in-hole E (t if0 number_1 e_1 e_2))
          (in-hole E e_2)
          "if0_false"
          (side-condition (not (equal? 0 (term number_1)))))
     (--> (in-hole E (t + number ...))
          (in-hole E (sum number ...))
          "addition")
     (--> (in-hole E (t_1 (t_2 λ x e) v))
          (in-hole E (subs x v e))
          "beta")
     (--> (in-hole E (t_1 (t_2 λ x e) v_1 v_2 v_s ...))
          (in-hole E (t_1 (subs x v_1 e) v_2 v_s ...))
          "beta2")
     (--> (in-hole E (t rec x e))
          (in-hole E (subs x (t rec x e) e))
          "rec")))
  
  (define-metafunction Mirror
    sum : number ... -> number
    [(sum number ...) ,(apply + (term (number ...)))])
  
;  (define-macro-aware-language Mirror* Mirror e E)
;  (define green (macro-aware-reduction-relation red Mirror* v E))
  
  (define-syntax-rule (test-eval t)
    (begin
      (macro-aware-eval Mirror red (user-term t))
      #f))
  
  (define-macro and () ()
    ((and)          0)
    ((and x)        x)
    ((and x xs ...) (if0 x (and xs ...) 7)))
  
  (define-macro let () ()
    [(_ [(var val) ...] body)
     
  
  (define-macro letrec () (let)
    [(_ ((var init) ...) body)
      (let ((var 'undefined) ...)
        (let ((var (let ((temp init)) (lambda () (set! var temp))))
              ...
              (bod (lambda () body)))
          (var) ... (bod)))])
  
  (define-macro oneplusone () ()
    ((oneplusone) (+ 1 1)))
  
  (define-macro inc () ()
    ((inc x) (+ x 1)))
  
  (define-macro two () (inc)
    ((two) (inc 1)))
  
  (define-macro three () (inc two)
    ((three) (inc (two))))
  
  (define-macro six () (inc two three)
    ((six) (+ (inc (two)) (three))))
  
  (define-macro cond0 (else) ()
    [(_ (^ else x))    x]
    [(_ (^ x y))       (if0 x y (+ 0 0))]
    [(_ (^ x y) z ...) (if0 x y (cond0 z ...))])
  
  (test-eval (+ 1 2))
  (test-eval (two))
  (test-eval (+ 1 (inc (+ 1 1))))
  (test-eval (inc (inc (inc 1))))
  (test-eval (two))
  (test-eval (three))
  (test-eval (six))
  (test-eval (+ 1 (cond0 (^ (+ 1 2) (+ 1 2)) (^ (+ 1 -1) (+ 3 4)))))
  (test-eval (+ 1 (cond0 (^ (+ 1 2) (+ 1 2)))))
  #|
  t
  (apply-reduction-relation green (list 'tag 3 777 777))
  (apply-reduction-relation green (list 'tag '(+ 1 2) 77 77))
  (apply-reduction-relation green (list '+ (list 'tag 1 7 7) 2))
  (apply-reduction-relation green (list (list 'tag '+ 7 7) 1 2))
  (apply-reduction-relation green (term (+ 1 2)))
  t
  (show-term (expand-term t))
  (unexpand-term (expand-term t))
  (macro-aware-step Mirror* green t)
  ;(apply-reduction-relation green (expand-term t))
  ;(macro-aware-step Mirror* green t)
  ;(apply-reduction-relation green t)
  ;(macro-aware-step Mirror* green t)
  ;(macro-aware-eval Mirror* green t)
  |#

  (display "ok")
)