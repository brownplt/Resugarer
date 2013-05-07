#lang racket

;; From Matthias Fellieson.

(require redex redex/tut-subst)
(module+ test (require rackunit))

;; -----------------------------------------------------------------------------
;; a simple core language, modeling imperative Racket

(define-language Core
  (p ::= (in (d ...) e))
  (d ::= (define x f))
  (e ::=
     n
     x
     (λ (x) e)
     (e e)
     (set! x e))
  (n ::= number)
  (f ::= n (λ (x) e))
  (x ::= variable-not-otherwise-mentioned))

(define p1 '(in ((define f (λ (x) 1))) ((λ (_) (f 2)) (set! f (λ (x) x)))))

(module+ test (check-true (redex-match? Core p p1)))

;; -----------------------------------------------------------------------------
;; evaluation semantics for the Core

(define-extended-language ECore Core
  (D ::= (in (d ...) E))
  (E ::= hole (f E) (E e) (set! x E))
  (e ::= .... (local (d) e))) ;[Justin]

(define ->c
  (reduction-relation
   ECore
   #:domain p
   [--> (in ((define x_1 f_1) ...) (in-hole E ((λ (x) e) f)))
        (in ((define x_1 f_1) ... (define x_* f)) (in-hole E (subst x_* x e)))
        (where x_* ,(variable-not-in (term (x_1 ...)) 'x))
        beta-s]
   [--> (in (d ...) (in-hole E (set! x f)))
        (in (set x f (d ...)) (in-hole E 42))
        set]
   [--> (in (d ...) (in-hole E x))
        (in (d ...) (in-hole E (look x (d ...))))
        reference]))

(define-metafunction ECore
  look : x (d ...) -> f
  [(look x ((define x_1 f_1) ... (define x f) (define x_2 f_2) ...))
   f
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define-metafunction ECore
  set : x f_new (d ...) -> (d ...)
  [(set x f_new ((define x_1 f_1) ... (define x f) (define x_2 f_2) ...))
   ((define x_1 f_1) ... (define x f_new) (define x_2 f_2) ...)
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define-metafunction ECore
  subst : e x e -> e
  [(subst e_new x e)
   ,(subst/proc (redex-match? ECore x) `(,(term x)) `(,(term e_new)) (term e))])

(module+ test
  (check-equal?
   (term (look w ((define y 0) (define w 1) (define w 2) (define z 3))))
   1)

  (check-equal?
   (term (set w 42 ((define y 0) (define w 1) (define w 2) (define z 3))))
   (term ((define y 0) (define w 42) (define w 2) (define z 3))))

  (check-equal? (term (subst 1 x 2)) 2)

  (check-true
   (redex-match? ECore ((in (d ...) 2)) (apply-reduction-relation* ->c p1))))

;; to visualize:
;; (traces ->c p1)

;; -----------------------------------------------------------------------------
;; extending the Core with syntactic sugar

(define-extended-language Surface Core
  (e ::= .... (local (d) e)))

(define p2
  (term
   (in ()
       (local ((define sin (λ (x) 1)))
         ((λ (_) (sin 2)) (set! sin (λ (x) x)))))))

(module+ test (check-true (redex-match? Surface p p2)))

;; treating it as a

(define-metafunction Surface
  φ : p -> p
  [(φ (in ((define x f) ...) e)) (in ((define x (φ-e f)) ...) (φ-e e))])

(define-metafunction Surface
  φ-e : e -> e
  [(φ-e x) x]
  [(φ-e n) n]
  [(φ-e (λ (x) e)) (λ (x) (φ-e e))]
  [(φ-e (set! x e)) (set! x (φ-e e))]
  [(φ-e (e_f e_a)) ((φ-e e_f) (φ-e e_a))]
  [(φ-e (local ((define x f)) e)) ((λ (x) ((λ (x_new) (φ-e e)) (set! x f))) 42)])

(define q (term (φ ,p2)))

(module+ test
  (check-true (redex-match? Core p q))

  (check-true
   (redex-match? ECore ((in (d ...) 2)) (apply-reduction-relation* ->c q))))

;; to visualize
;; (traces ->c q)

;; -----------------------------------------------------------------------------
;; evaluation semantics I for the Surface: use substitution and Y for functions
;; flawed if x is assignable in e or e_b (I think)

(define-extended-language ESurfaceI ECore)

(define Yv (term (λ (f) (f 42)))) ;; forgive me for not filling in the blanks

(define ->sI
  (reduction-relation
   ESurfaceI
   ; #:domain p
   [--> (in ((define x_1 f_1) ...) (in-hole E ((λ (x) e) f)))
        (in ((define x_1 f_1) ... (define x_* f)) (in-hole E (subst x_* x e)))
        (where x_* ,(variable-not-in (term (x_1 ...)) 'x))
        beta-s]
   [--> (in (d ...) (in-hole E (local ((define x n)) e)))
        (in (d ...) (in-hole E (subst n x e)))
        let]
   [--> (in (d ...) (in-hole E (local ((define x (λ (x_p) e_b))) e)))
        (in (d ...) (in-hole E (subst (,Yv (λ (x) (λ (x_p) e_b))) x e)))
        fix]
   [--> (in (d ...) (in-hole E (set! x f)))
        (in (set x f (d ...)) (in-hole E 42))
        set]
   [--> (in (d ...) (in-hole E x))
        (in (d ...) (in-hole E (look x (d ...))))
        reference]))

;; this one fails, I would have to define subst on terms with set!
#;
(check-true
 (redex-match? ECore ((in (d ...) 2)) (apply-reduction-relation* ->sI p2)))

;; -----------------------------------------------------------------------------
;; evaluation semantics II for the Surface: use Barendregt,
;; flawed if x is assignable in e or e_b (I think)

(define-extended-language ESurfaceII ECore)

(define ->sII
  (reduction-relation
   ESurfaceII
   ; #:domain p
   [--> (in ((define x_1 f_1) ...) (in-hole E ((λ (x) e) f)))
        (in ((define x_1 f_1) ... (define x_* f)) (in-hole E (subst x_* x e)))
        (where x_* ,(variable-not-in (term (x_1 ...)) 'x))
        beta-s]
   [--> (in (d ...) (in-hole E (local ((define x f)) e)))
        (in (d ... (define x_new f)) (in-hole E (subst x_new x e))) ;[Justin]
        (where x_new ,(variable-not-in
                       (term (in (d ...) (in-hole E (local ((define x f)) e))))
                       'x))
        local]
   [--> (in (d ...) (in-hole E (set! x f)))
        (in (set x f (d ...)) (in-hole E 42))
        set]
   [--> (in (d ...) (in-hole E x))
        (in (d ...) (in-hole E (look x (d ...))))
        reference]))

(module+ test
  (check-true
   (redex-match? ECore ((in (d ...) 2)) (apply-reduction-relation* ->sII p2))))

;; to visualize
;; (traces ->sII p2)