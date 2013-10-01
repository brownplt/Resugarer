#lang racket

(require redex)
(require "resugar-redex.rkt")
(require "lang-min.rkt")


;;; Booleans ;;;

(define-macro True
  [(True)
   (λ a (λ b a))])

(define-macro False
  [(False)
   (λ a (λ b b))])

(define-macro If
  [(If x y z)
   (apply (apply x y) z)])

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

#|(define-macro Plus ; doesn't work
  [(Plus n m)
   (Letrec plus
           (λ n (λ m (If (Zero? n) m (apply plus (Decr n) (! S m)))))
           (apply (apply plus n) m))]) |#

(test-eval (If (Not (True)) (Not (True)) (Not (False))))
(test-eval (And (Or (True) (False)) (Or (False) (False))))
(test-eval (Snd (Fst (Pair (Pair (True) (False)) (Pair (False) (True))))))

(test-eval (Zero? (Zero)))
(test-eval (Zero? (S (S (Zero)))))
(test-eval (Zero? (Decr (Decr (S (S (Zero)))))))

