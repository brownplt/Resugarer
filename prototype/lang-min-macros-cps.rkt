#lang racket

(require redex)
(require "resugar-redex.rkt")
(require "lang-min.rkt")


(define-macro Let
  [(Let x e b)
   (apply (lambda x b) e)])

(define-macro CpsM
  [(CpsM ($λ x y))
   (lambda x (lambda k_ (! CpsT y k_)))]
  [(CpsM x)
   (begin x)])

(define-macro CpsT
  [(CpsT ($apply x y) k)
   (CpsT x (! lambda f_ (CpsT y (lambda e_ (apply f_ e_ k)))))]
  [(CpsT x k_)
   (Let k k_
   (apply k (CpsM x)))])

(define-macro Cps
  [(Cps x) (Let halt (lambda h_ h_) (CpsT x halt))])

(define-macro CpsM*
  [(CpsM* ($λ v e))
   (lambda v (lambda k (CpsC* e k)))]
  [(CpsM* x) x])

(define-macro CpsC*
  [(CpsC* ($λ v e) c)
   (apply c (CpsM* ($λ v e)))]
  [(CpsC* ($apply f e) c)
   (CpsK* f (lambda f_ (CpsK* e (lambda e_ (apply f_ e_ c)))))]
  [(CpsC* x c)
   (apply c (CpsM* x))])

(define-macro CpsK*
  [(CpsK* ($λ v e) k)
   (apply k (CpsM* ($λ e)))]
  [(CpsK* ($apply f e) k)
   (CpsK* f (lambda f_ (CpsK* e (lambda e_ (apply f_ e_ k)))))]
  [(CpsK* x c)
   (apply c (CpsM* x))])

(define-macro Fischer
  [(Fischer ($λ x y))
   (lambda k (apply k
     (! lambda x (! lambda k (! apply (Fischer y) (! lambda m (apply k m)))))))]
  [(Fischer ($apply x y))
   (lambda k (! apply (Fischer x) (! lambda m (! apply (Fischer y)
     (! lambda n (apply (apply m n) (lambda a (apply k a))))))))]
  [(Fischer x)
   (lambda k (! apply k x))])


(test-eval (Cps ($apply ($λ x (+ x 1)) 3)))
(test-eval (Cps ($apply ($apply ($λ f ($λ x ($apply f ($apply f x))))
                                ($λ x (+ x 1)))
                        (+ 1 2))))
;(test-eval (CpsT ($apply ($apply ($λ f ($λ x ($apply f ($apply f x))))
;                                   ($λ x (+ x 1)))
;                          (+ 1 2)) (lambda h h)))
;(test-eval (Cps ($apply ($λ f ($apply f 1)) ($λ x (+ x 1)))))
;(test-eval (CpsK* ($apply ($λ f ($apply f 1)) ($λ x (+ x 1)))
;                  (lambda h h)))
;(test-eval (Lets [^ [^ x 1] [^ y (+ 1 2)]] (+ x y)))

;(test-eval (apply (Fischer ($apply ($λ x (+ x 1)) 3)) (lambda h h)))
;(test-eval (apply (Fischer ($apply ($apply ($λ f ($λ x ($apply f ($apply f x))))
;                                   ($λ x (+ x 1)))
;                          (+ 1 2))) (lambda h h)))