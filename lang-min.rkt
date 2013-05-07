#lang racket

; Assembled from Matthias' letrec (personal correspondence)
; and redex/example/letrex.rkt.
; The language is probably mostly correct.

(require rackunit)
(require redex)
(require "resugar.rkt")


  ;;;;;;;;;;;;;;;;
  ;;; Language ;;;
  ;;;;;;;;;;;;;;;;


(define-language Min
  (p ((store (x v) ...) e))
  (e (apply o e ...)
     (+ o e ...)
     (set! o x e)
     (begin o e e ...)
     (if o e e e)
     (rec x e)
     x
     v)
  (v (lambda o x e)
     number
     boolean)
  (x variable-not-otherwise-mentioned)
  (pc ((store (x v) ...) ec))
  (ec (apply o ec e)
      (apply o v ec)
      (set! o variable ec)
      (begin o ec e e ...)
      (if o ec e e)
      hole)
  (o (origins any)))

(define-metafunction Min
  swap : x x any -> any
  [(swap x_1 x_2 x_1) x_2]
  [(swap x_1 x_2 x_2) x_1]
  [(swap x_1 x_2 (any_1 ...)) ((swap x_1 x_2 any_1) ...)]
  [(swap x_1 x_2 any_1) any_1])

(define-metafunction Min
  subs : x e e -> e
  [(subs x_1 e_1 (lambda o x_1 e_2))
   (lambda o x_1 e_2)]
  [(subs x_1 e_1 (lambda o x_2 e_2))
   ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
              (term (lambda o x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]
  [(subs x_1 e_1 (set! o x_1 e_2))
   (set! o x_1 e_2)]
  [(subs x_1 e_2 (set! o x_2 e_2))
   ,(term-let [[x_new (variable-not-in (term e1) (term x_2))]]
              (term (set! o x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]
  [(subs x_1 e_1 (rec o x_2 e_2))
   ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
              (term (rec o x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]  
  [(subs x_1 e_1 x_1) e_1]
  [(subs x_1 e_1 x_2) x_2]
  [(subs x_1 e_1 (apply o e_2 ...))
   (apply o (subs x_1 e_1 e_2) ...)]
  [(subs x e number) number]
  [(subs x e boolean) boolean]
  [(subs x e (+ o e_1 ...)) (+ o (subs x e e_1) ...)]
  [(subs x e (if o e_1 e_2 e_3))
   (if o (subs x e e_1) (subs x e e_2) (subs x e e_3))]
  [(subs x e (begin o e_1 ...))
   (begin o (subs x e e_1) ...)])

(define-metafunction Min
  sum : number ... -> number
  [(sum number ...) ,(apply + (term (number ...)))])

(define-metafunction Min
  look : x (store (x v) ...) -> v
  [(look x (store (x_1 v_1) ... (x v) (x_2 v_2) ...))
   v
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define-metafunction Min
  set : x v_new (store (x v) ...) -> (store (x v) ...)
  [(set x v_new (store (x_1 v_1) ... (x v) (x_2 v_2) ...))
   (store (x_1 v_1) ... (x v_new) (x_2 v_2) ...)
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define red
  (reduction-relation
   Min
   (--> (in-hole pc_1 (begin o v e_1 e_2 ...))
        (in-hole pc_1 (begin o e_1 e_2 ...))
        "begin many")
   
   (--> (in-hole pc_1 (begin o e_1))
        (in-hole pc_1 e_1)
        "begin one")
   
   (--> (in-hole pc_1 (+ o number ...))
        (in-hole pc_1 (sum number ...))
        "addition")
   
   (--> ((store (x_1 v_1) ...) (in-hole ec x))
        ((store (x_1 v_1) ...) (in-hole ec (look x (store (x_1 v_1) ...))))
        "deref")
   
   (--> ((store (x_1 v_1) ...)           (in-hole ec (set! o x v)))
        ((set x v (store (x_1 v_1) ...)) (in-hole ec v))
        "set!")

   (--> ((store (x_1 v_1) ...)           (in-hole ec (apply o_1 (lambda o_2 x e) v)))
        ((store (x_1 v_1) ... (x_new v)) (in-hole ec (subs x x_new e)))
        (where x_new ,(variable-not-in (term (x_1 ...)) 'x))
        "beta")))

   ;with [(--> a ,(collect (term b))) (==> a b)]))


(define (run-traces e)
  (traces red `((store) ,e)))

(define (run-eval e)
  (car (apply-reduction-relation* red `((store) ,e))))

(define o '(origins #f))

(run-eval `(apply ,o (lambda ,o x x) 3))
(run-eval `(+ ,o 2 3))
(run-eval `(apply ,o (lambda ,o x (begin ,o (set! ,o x 1) x)) 3))
(run-eval `(apply ,o (lambda ,o x (apply ,o (lambda ,o x x) 2)) 1))


  ;;;;;;;;;;;;;;
  ;;; Macros ;;;
  ;;;;;;;;;;;;;;


(define-macro let () ()
  [(let x e b)
   (apply (lambda x b) e)])

(define-syntax-rule (test-eval t)
  (macro-aware-eval Min red (make-pattern t) #t))

(test-eval (+ 1 2))
(test-eval (let x 3 (+ x x)))


#|
(run '(letrec ((f (lambda (x)
                    (letrec ((y (f 1))) 
                      2))))
        (f 3)))

(run '(letrec ((f (lambda (x)
                    (letrec ((y 1))
                      (f 1)))))
        (f 3)))
|#