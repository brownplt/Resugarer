#lang racket

(require rackunit)
(require redex)
;(require "utility.rkt")
;(require "pattern.rkt")
;(require "macro.rkt")
;(require "resugar.rkt")
(require "resugar-redex.rkt")


  ;;;;;;;;;;;;;;;;
  ;;; Language ;;;
  ;;;;;;;;;;;;;;;;


(define-macro-aware-language Mirror
  [e (apply e ...)
     (+ e ...)
     (if0 e e e)
     (rec x e)
     x
     v]
  [v (λ x e)
     number]
  [E (apply v ... E e ...)
     (if0 E e e)
     (+ v ... E e ...)
     hole]
  [x variable-not-otherwise-mentioned])

(define-metafunction Mirror
  swap : x x any -> any
  [(swap x_1 x_2 x_1) x_2]
  [(swap x_1 x_2 x_2) x_1]
  [(swap x_1 x_2 (any_1 ...)) ((swap x_1 x_2 any_1) ...)]
  [(swap x_1 x_2 any_1) any_1])

(define-metafunction Mirror
  subs : x e e -> e
  [(subs x_1 e_1 (λ o x_1 e_2))
   (λ o x_1 e_2)]
  [(subs x_1 e_1 (λ o x_2 e_2))
   ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
              (term (λ o x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]
  [(subs x_1 e_1 (rec o x_2 e_2))
   ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
              (term (rec o x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]
  [(subs x_1 e_1 x_1) e_1]
  [(subs x_1 e_1 x_2) x_2]
  [(subs x_1 e_1 (apply o e_2 ...))
   (apply o (subs x_1 e_1 e_2) ...)]
  [(subs x e number) number]
  [(subs x e (+ o e_1 ...)) (+ o (subs x e e_1) ...)]
  [(subs x e (if0 o e_1 e_2 e_3))
   (if0 o (subs x e e_1) (subs x e e_2) (subs x e e_3))])
  
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
  
(define (red-step t) (apply-reduction-relation red t))

(define-metafunction Mirror
  sum : number ... -> number
  [(sum number ...) ,(apply + (term (number ...)))])
  
  
  ;;;;;;;;;;;;;;
  ;;; Macros ;;;
  ;;;;;;;;;;;;;;
  
  
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


  ;;;;;;;;;;;;;;;
  ;;; Testing ;;;
  ;;;;;;;;;;;;;;;


(define MAMirror
  (make-redex-language "Mirror" Mirror red (λ (x y) x) (λ (x) (cons x 'nuthin))))

(define-syntax-rule (test-eval t)
  (macro-aware-eval MAMirror (make-pattern t) 'nuthin #t))

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
(test-eval (cond0 (^ 0 (+ 1 2))))
(test-eval (cond0 (^ (+ 1 2) (+ 1 2))))
(test-eval (cond0 (^ 1 2) (^ 3 4)))
(test-eval (+ 1 (cond0 (^ (+ 1 2) (+ 1 2)) (^ (+ 1 -1) (+ 3 4)))))
(test-eval (+ 1 (cond0 (^ (+ 1 2) (+ 1 2)))))
(test-eval (+ 1 (cond0 (^ (+ 1 2) (+ 1 2)) (^ (+ 1 1) (+ 3 4)))))
(test-eval (apply (λ x (apply x x)) (λ y y)))

(display "ok")