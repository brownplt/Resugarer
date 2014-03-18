#lang racket

(require redex)
(require "resugar-redex.rkt")
(require "lang-min.rkt")


;;; Let ;;;

(define-macro Let
  [(Let x e b)
   (apply (lambda x b) e)])

(define-macro Letrec
  [(Letrec x e b)
   (Let x 0 (begin (set! x e) b))])

(define-macro Letrecs
  [(Letrecs [^ [^ x e] ...] b)
   (Lets [^ [^ x 0] ...]
         (begin (set! x e) ... b))])

(define-macro Lets
  [(Lets [^ [^ x e]] b)
   (apply (lambda x b) e)]
  [(Lets [^ [^ x e] y ys ...] b)
   (apply (lambda x (! Lets [^ y ys ...] b)) e)])


;;; Thunks ;;;

(define-macro Thunk
  [(Thunk body)
   (λ unused body)])

(define-macro Force
  [(Force thunk)
   (apply thunk "unused")])


;;; Booleans ;;;

(define-macro True
  [(True)
   (λ a (λ b a))])

(define-macro False
  [(False)
   (λ a (λ b b))])

(define-macro If
  [(If x y z)
   (Force (apply x (Thunk y) (Thunk z)))])

(define-macro Not
  [(Not x)
   (If x (! False) (! True))])

(define-macro And
  [(And x y)
   (If x y (! False))])

(define-macro Or
  [(Or x y)
   (Not (And (Not x) (Not y)))])


;;; Pairs ;;;

(define-macro Pair
  [(Pair x y)
   (λ z (apply (apply z x) y))])

(define-macro Fst
  [(Fst p)
   (apply p (True))])

(define-macro Snd
  [(Snd p)
   (apply p (False))])


;;; Numerals ;;;

; Construction
(define-macro Zero
  [(Zero)
   (Pair (! True) (True))])

(define-macro S
  [(S n)
   (Pair (! False) n)])

; Destruction
(define-macro Zero?
  [(Zero? n)
   (Fst n)])

(define-macro Decr
  [(Decr n)
   (Snd n)])


(test-eval (If (Not (True)) (Not (True)) (Not (False))))
(test-eval (And (Or (True) (False)) (Or (False) (False))))
(test-eval (Snd (Fst (Pair (Pair (True) (False)) (Pair (False) (True))))))

(test-eval (Zero? (Zero)))
(test-eval (Zero? (S (S (Zero)))))
(test-eval (Zero? (Decr (Decr (S (S (Zero)))))))

#| addition?
(define-macro Plus ; doesn't work
  [(Plus n m)
   (Letrec plus
           (λ n (λ m (If (Zero? n) m (apply plus (Decr n) (S m)))))
           (apply plus n m))])
(test-eval
 (Letrec plus
         (! λ n (λ m (If (Zero? n) m (apply plus (! Decr n) (! S m)))))
         (apply plus (S (S (Zero))) (S (Zero)))))
(test-eval (Plus (S (S (Zero))) (S (Zero))))
|#