#lang racket

; Assembled from Matthias' letrec (personal correspondence)
; and redex/example/letrex.rkt.
; The language is probably mostly correct.

(require rackunit)
(require redex)
(require "resugar-redex.rkt")


  ;;;;;;;;;;;;;;;;
  ;;; Language ;;;
  ;;;;;;;;;;;;;;;;


(define-language Min
  (p (top s e))
  (e (apply o e ...)
     (op o e ...)
     (set! o x e)
     (begin o e e ...)
     (if o e e e)
     (rec x e)
     x
     v)
  (op + cons first rest empty? eq?)
  (s (store (x v) ...))
  (v (lambda o x e)
     number
     boolean
     string
     empty
     (cons o v v))
  (x variable-not-otherwise-mentioned)
  (pc (top (store (x v) ...) ec))
  (ec (apply o ec e)
      (apply o v ec)
      (op o v ... ec e ...)
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
;  [(subs x e (+ o e_1 ...)) (+ o (subs x e e_1) ...)]
  [(subs x e (if o e_1 e_2 e_3))
   (if o (subs x e e_1) (subs x e e_2) (subs x e e_3))]
  [(subs x e (begin o e_1 ...))
   (begin o (subs x e e_1) ...)]
  [(subs x e (op o e_1 ...))
   (op o (subs x e e_1) ...)])

;(define-metafunction Min
;  sum : number ... -> number
;  [(sum number ...) ,(apply + (term (number ...)))])

(define-metafunction Min
  look : x (store (x v) ...) -> v
  [(look x (store (x_1 v_1) ... (x v) (x_2 v_2) ...))
   v
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define-metafunction Min
  set : x v (store (x v) ...) -> (store (x v) ...)
  [(set x v_new (store (x_1 v_1) ... (x v) (x_2 v_2) ...))
   (store (x_1 v_1) ... (x v_new) (x_2 v_2) ...)
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define red
  (reduction-relation
   Min
   (--> (in-hole pc_1 (begin o v e_1 e_2 ...))
        (in-hole pc_1 (begin o e_1 e_2 ...))
        "begin-many")
   
   (--> (in-hole pc_1 (begin o e_1))
        (in-hole pc_1 e_1)
        "begin-one")
 
   (--> (in-hole pc (empty? o empty))               (in-hole pc #t))
   (--> (in-hole pc (empty? o (cons o_1 v_1 v_2)))  (in-hole pc #f))
   (--> (in-hole pc (+ o v ...))                    (in-hole pc ,(apply + (term (v ...)))))
   (--> (in-hole pc (eq? o v_1 v_2))                (in-hole pc ,(eq? (term v_1) (term v_2))))
   (--> (in-hole pc (first o_1 (cons o_2 v_1 v_2))) (in-hole pc v_1))
   (--> (in-hole pc (rest o_1 (cons o_2 v_1 v_2)))  (in-hole pc v_2))
   
;   (--> (in-hole pc_1 (+ o number ...))
;        (in-hole pc_1 (sum number ...))
;        "plus")
   
   (--> (top s (in-hole ec x))
        (top s (in-hole ec (look x s)))
        "variable")
   
   (--> (top s           (in-hole ec (set! o_2 x v)))
        (top (set x v s) (in-hole ec v))
        "set!")

   (--> (top (store (x_1 v_1) ...)
             (in-hole ec (apply o_1 (lambda o_2 x e) v)))
        (top (store (x_1 v_1) ... (x_new v))
             (in-hole ec (subs x x_new e)))
        (where x_new ,(variable-not-in (term (x_1 ...)) 'x))
        "apply")
  
   (--> (in-hole pc (if o #t e_1 e_2))
        (in-hole pc e_1)
        "if-true")
  
   (--> (in-hole pc (if o #f e_1 e_2))
        (in-hole pc e_2)
        "if-false")))

   ;with [(--> a ,(collect (term b))) (==> a b)]))


  ;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Language Testing ;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;


(define (run-eval e)
  (third (car (apply-reduction-relation* red `(top (store) ,e)))))

(define o '(origins #f))

(define-syntax-rule
  (eval-tests [actual expected] ...)
  (begin (check-equal? (run-eval actual) expected) ...))

(eval-tests
 [`(apply ,o (lambda ,o x x) 3) 3]
 [`(+ ,o 2 3) 5]
 [`(eq? ,o "a" "a") #t]
 [`(eq? ,o "a" "b") #f]
 [`(empty? ,o empty) #t]
 [`(empty? ,o (cons ,o "a" "b")) #f]
 [`(cons ,o (+ ,o 1 2) (+ ,o 3 4)) `(cons ,o 3 7)]
 [`(+ ,o (+ ,o 1 2) (+ ,o 3 4)) 10]
 [`(rest ,o (first ,o (cons ,o (cons ,o "a" (cons ,o "b" empty)) "c")))
  `(cons ,o "b" empty)]
 [`(apply ,o (lambda ,o x (begin ,o (set! ,o x 1) x)) 3)    1]
 [`(apply ,o (lambda ,o x (apply ,o (lambda ,o x x) 2)) 1)  2]
 [`(apply ,o (lambda ,o x (+ ,o x 1)) (+ ,o 1 2))           4]
 [`(begin ,o (+ ,o 1 2) (+ ,o 3 4) (+ ,o 5 6))             11]
 [`(if ,o #t 1 2) 1]
 [`(if ,o #f 1 2) 2]
 )

#|
  ;;;;;;;;;;;;;;
  ;;; Macros ;;;
  ;;;;;;;;;;;;;;

(define MAMin
  (redex-language "Min" Min red
                  (λ (expr store) `(top ,store ,expr))
                  (λ (top) (cons (third top) (second top)))))

(define-syntax-rule (test-eval p)
  (macro-aware-eval MAMin (make-pattern p) (term (store)) #t))



(define-macro let () ()
  [(let x e b)
   (apply (lambda x b) e)])

(define-macro letrec () (let)
  [(letrec x e b)
   (let x 0 (begin (set! x e) b))])

(define-macro cond (else) ()
  [(cond) 0]
  [(cond [^ x y] xs ...) (if x y (cond xs ...))]
  [(cond [^ else x]) x])

(define-macro process-state (accept ->) ()
  [(_ accept)
   (lambda (stream)
     (cond
       [^ (empty? stream) #t]
       [^ else #f]))]
  [(_ [^ label -> target] ...)
   (lambda (stream)
     (cond
       [^ (empty? stream) #f]
       [^ (eq? label (first stream)) (target (rest stream))]
       ...
       [else #f]))])

(define-macro automaton (:) (process-state)
  [(_ init-state
    [^ state : response ...]
    ...)
   (letrec [^ [^ state (process-state response ...)] ...]
     init-state)])

(test-eval (+ 1 2))
(test-eval (apply (lambda x (+ x 1)) (+ 1 2)))
(test-eval (let x 3 (+ x x)))
(test-eval (letrec x (lambda y x) (apply x 6)))
#|
(test-eval
 ((let M (automaton
          init
          [init : [c -> more]]
          [more : [a -> more]
                  [d -> more]
                  [r -> end]]
          [end :  accept])
    (M (cons 'c (cons 'a (cons 'd (cons 'r empty))))))))
|#

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
|#