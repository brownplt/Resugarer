(module resugar racket
  (require rackunit)
  (require redex)
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  
  (define-syntax-rule (test-patt t)
    (sexpr->pattern 't (all-macro-literals) (all-macro-names) (list)))
  
  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)))

  ; Assume that Redex terms all have the form
  ; | (label origins x ...)
  ; | atom 
  ; where 'label' identifies the term type, e.g. λ, if, apply,
  ; 'origins' is a list of pattern origins,
  ; and 'x ...' are either subterms, having the same form.
  
  (define (term->pattern t)
    (define (origs->tags os p)
      (match os 
        [(list) p]
        [(cons o os) (tag (origs->tags os p) o)]))
    (match t
      [(? atomic? t)
       (constant t)]
      [(cons l (cons (list 'origins os) ts))
       (origs->tags os
         (plist (t-apply) (cons (constant l) (map term->pattern ts))))]))

  (define (pattern->term p)
    (define (strip-tags p)
      (match p
        [(constant l) l]
        [(tag p _) (strip-tags p)]))
    (match p
      [(constant c) c]
      [(plist (t-apply) (cons l ps))
       (cons (strip-tags l)
             (cons (list 'origins (list))
                   (map pattern->term ps)))]
      [(tag p o)
       (match (pattern->term p)
         [(cons l (cons (list 'origins os) ts))
          (cons l (cons (list 'origins (cons o os)) ts))]
         [(? atomic? t) t])]))
  
  (define (show-term t)
    (match t
      [(? atomic? t)
       (show t)]
      [(cons l (cons (list 'origins o) ts))
       (format "(~a)" (string-join (cons (symbol->string l)
                                         (map show-term ts)) " "))]))
  
  (define (expand-patt p) ; pattern -> term
    (pattern->term (expand p)))
  
  (define (unexpand-patt t) ; term -> pattern
    (unexpand (term->pattern t)))
  
  (define (macro-aware-step lang red p)
    (display (show-pattern p)) (display "\n")
    (define (catmap f xs) (append* (map f xs)))
    (define (step t) (apply-reduction-relation red t))
    (define (new-step t) (catmap resugar (step t)))
    (define (resugar t)
      (let ((p (unexpand-patt t)))
        (if p (list p) (begin (display (format "SKIP ~a\n" (show-term t)))
                              (new-step t)))))
    (new-step (expand-patt p)))
  
  (define (macro-aware-eval lang red p)
    ;(display (format "\t~a\n" (show-pattern p)))
    (let ((next-patts (macro-aware-step lang red p)))
      (cons (show-pattern p #t)
            (if (empty? next-patts)
                (list)
                (macro-aware-eval lang red (car next-patts))))))
  
  
  ;;; Testing ;;;
  
  (define-language Mirror
    [e (apply o e ...)
       (+ o e ...)
       (if0 o e e e)
       (rec o x e)
       x
       v]
    [v (λ o x e)
       number]
    [E (apply o v ... E e ...)
       (if0 o E e e)
       (+ o v ... E e ...)
       hole]
    [x variable-not-otherwise-mentioned]
    [o (origins any)])
  
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
     (--> (in-hole E (if0 o 0 e_1 e_2))
          (in-hole E e_1)
          "if0_true")
     (--> (in-hole E (if0 o number_1 e_1 e_2))
          (in-hole E e_2)
          "if0_false"
          (side-condition (not (equal? 0 (term number_1)))))
     (--> (in-hole E (+ o number ...))
          (in-hole E (sum number ...))
          "addition")
     (--> (in-hole E (apply o_1 (λ o_2 x e) v))
          (in-hole E (subs x v e))
          "beta")
     (--> (in-hole E (apply o_1 (λ o_2 x e) v_1 v_2 v_s ...))
          (in-hole E (apply o_1 (subs x v_1 e) v_2 v_s ...))
          "beta2")
     (--> (in-hole E (rec o x e))
          (in-hole E (subs x (rec o x e) e))
          "rec")))
  
  (define-metafunction Mirror
    sum : number ... -> number
    [(sum number ...) ,(apply + (term (number ...)))])
  
  (define-syntax-rule (test-eval t)
    (begin
      (macro-aware-eval Mirror red (test-patt t))
      #f))
  
  (define-macro and () ()
    ((and)          0)
    ((and x)        x)
    ((and x xs ...) (if0 x (and xs ...) 7)))
  
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
  
  
  
  (define-syntax-rule (test-conversion t)
    (check-equal? (pattern->term (term->pattern (term t)))
                  (term t)))
  
  (test-conversion (+ (origins ()) 1 2))
  (test-conversion (if0 (origins (a b)) (+ (origins (b a)) x 3) 5 6))
  
  ;(expand-patt (term->pattern (term (+ (origins ()) 1 2))))
  
  (define t (term (+ (origins ()) 1 2)))
  (test-eval (+ 1 2))
  (test-eval (inc 1))
  (test-eval (inc (inc 3)))
  (test-eval (two))
  (test-eval (three))
  (test-eval (+ 1 (inc (+ 1 1))))
  (test-eval (inc (inc (inc 1))))
  (test-eval (two))
  (test-eval (six))
  #|
  (test-eval (+ 1 (cond0 (^ (+ 1 2) (+ 1 2)) (^ (+ 1 -1) (+ 3 4)))))
  (test-eval (+ 1 (cond0 (^ (+ 1 2) (+ 1 2)))))
  t
  (apply-reduction-relation green (list 'tag 3 777 777))
  (apply-reduction-relation green (list 'tag '(+ 1 2) 77 77))
  (apply-reduction-relation green (list '+ (list 'tag 1 7 7) 2))
  (apply-reduction-relation green (list (list 'tag '+ 7 7) 1 2))
  (apply-reduction-relation green (term (+ 1 2)))
  t
  (show-term (expand-patt t))
  (unexpand-patt (expand-patt t))
  (macro-aware-step Mirror* green t)
  ;(apply-reduction-relation green (expand-patt t))
  ;(macro-aware-step Mirror* green t)
  ;(apply-reduction-relation green t)
  ;(macro-aware-step Mirror* green t)
  ;(macro-aware-eval Mirror* green t)
  |#

  (display "ok")
)