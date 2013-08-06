#lang racket

(require redex)
(require "resugar.rkt")
(require "resugar-racket.rkt")


(define-macro Let
  [(Let x e b)
   ((lambda (x) b) e)])



(define-macro CpsM*
  [(CpsM* (^ $λ v e))
   (! lambda (v k) (CpsC* e k))]
  [(CpsM* x) x])

(define-macro CpsC*
  [(CpsC* (^ $λ v e) c)
   (c (CpsM* (^ $λ v e)))]
  [(CpsC* (^ $apply f e) c)
   (CpsK* f (lambda (f_) (CpsK* e (lambda (e_) (! f_ e_ c)))))]
  [(CpsC* x c)
   (Let w (CpsM* x) (c w))
   #;(c (CpsM* x))])

(define-macro CpsK*
  [(CpsK* ($λ v e) k)
   (k (CpsM* (^ $λ e)))]
  [(CpsK* ($apply f e) k)
   (CpsK* f (lambda (f_) (CpsK* e (lambda (e_) (! f_ e_ (lambda (r_) (k r_)))))))]
  [(CpsK* x k)
   (k (CpsM* x))])

(define-macro Cps*
  [(Cps* x) (Let halt (lambda (h_) h_) (CpsC* x halt))])



(define-macro Fischer
  [(Fischer (^ $λ x y))
   (λ (k) (k (λ (x k) ((Fischer y) (λ (m) (k m))))))]
  [(Fischer (^ $apply x y))
   (λ (k) ((Fischer x) (λ (m) ((Fischer y) (λ (n) (m n (λ (a) (k a))))))))]
  [(Fischer x)
   (λ (k) (k x))])



(define-macro CpsApp
  [(CpsApp x y k)
   ((Cps x) (λ (m) ((Cps y) (λ (n) (m n (λ (a) (k a)))))))])

(define-macro Cps
  [(Cps (^ $λ x y))
   (λ (k) (k (λ (x k) ((Cps y) (λ (m) (k m))))))]
  [(Cps (^ $apply x y))
   (λ (k) (! CpsApp x y k))]
  [(Cps x)
   (λ (k) (! k x))])


#;(define-macro CpsM
  [(CpsM (^ $λ x y))
   (lambda (x k) (! AppCps k y))]
  [(CpsM x)
   (begin x)])

#;(define-macro AppCps
  [(AppCps k (^ $apply x y))
   (AppCps (lambda (f_) (AppCps (lambda (e_) (! f_ e_ k)) y)) x)]
  [(AppCps k x)
   (k (! CpsM x))])

#;(define-macro Cps
  [(Cps x) (Let halt (! lambda (h_) h_) (AppCps halt x))])

(define (term->expr t)
  (match t
    [(tlist os (list '^ '$apply f x))
     (tlist os (list 'apply f x))]
    [(tlist os (list '^ '$λ v x))
     (tlist os (list 'λ (tlist (list) (list 'v)) x))]
    [(tlist os ts)
     (tlist os (map term->expr ts))]))

(define (expr->term t)
  (match t
    [(tlist os (list 'apply f x))
     (tlist os (list '^ '$apply f x))]
    [(tlist os (list 'λ (tlist os2 (list v)) x))
     (tlist os (list '^ '$λ v x))]
    [(tlist os ts)
     (tlist os (map expr->term ts))]))

(set-debug-steps! #f)
(set-debug-vars! #f)
(set-debug-tags! #f)
(set-debug! #f)

(test-eval ((Cps (^ $apply (^ $λ x (+ x 1)) 3)) (λ (h) h)))
(test-eval ((Cps (^ $apply (^ $apply (^ $λ x (^ $λ y (+ x y))) 1) 2)) (λ (h) h)))
#|
  The core execution of the following takes 35 steps (vs. 12), including,
  (k (λ (f k) ((λ (k) (k (λ (x k) ((λ (k) ((λ (k) (k f)) (λ (m) ((λ (k) ((λ (k) (k f)) (λ (m) ((λ (k) (k x)) (λ (n) (m n (λ (a) (k a)))))))) (λ (n) (m n (λ (a) (k a)))))))) (λ (m) (k m)))))) (λ (m) (k m)))))
|#
(test-eval ((Cps (^ $apply (^ $apply (^ $λ f (^ $λ x (^ $apply f (^ $apply f x))))
                                (^ $λ x (+ x 1)))
                        (+ 1 2))) (λ (h) h)))
;(test-eval (Cps* (^ $λ x x)))
;(test-eval (Cps* (^ $apply (^ $λ x (+ x 1)) 3)))
;(test-eval ((Fischer (^ $apply (^ $λ x (+ x 1)) 3)) (λ (h_) h_)))
;(test-eval ((Fischer (^ $apply (^ $apply (^ $λ f (^ $λ x (^ $apply f (^ $apply f x))))
;                                   (^ $λ x (+ x 1)))
;                          (+ 1 2))) (lambda (h) h)))
;(test-eval (CpsT ($apply ($apply ($λ f ($λ x ($apply f ($apply f x))))
;                                   ($λ x (+ x 1)))
;                          (+ 1 2)) (Lambda h h)))
;(test-eval (Cps ($apply ($λ f ($apply f 1)) ($λ x (+ x 1)))))
;(test-eval (CpsK* ($apply ($λ f ($apply f 1)) ($λ x (+ x 1)))
;                  (Lambda h h)))
;(test-eval (Lets [^ [^ x 1] [^ y (+ 1 2)]] (+ x y)))

;(test-eval ((Fischer ($apply ($λ x (+ x 1)) 3)) (Lambda h h)))