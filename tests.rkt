#lang racket
(require "utility.rkt")
(require (except-in rackunit fail))
(require "pattern.rkt")
(require "macro.rkt")
(require "resugar.rkt")


;;;;;;;;;;;;
;; Syntax ;;
;;;;;;;;;;;;

(define test-lits '(else A B C))
(define test-macs '(cond and))
(define test-vars '(x y z xs ys zs))

(define test-origin (list))

(define-syntax-rule (test-pattern p)
  (sexpr->pattern 'p (list 'x 'xs 'y 'ys 'z 'zs)))

;(define-syntax-rule (test-template p)
;  (sexpr->template 'p test-vars))

(define-syntax test-subs-rhs
  (syntax-rules (@ @...)
    [(_ (@... (x ...) y (z ...)))
     (inter-ellipsis (t-apply)
                     (list (test-subs-rhs x) ...)
                     (test-subs-rhs y)
                     (list (test-subs-rhs z) ...))]
    [(_ (@ x ...))
     (inter-list (t-apply) (list (test-subs-rhs x) ...))]
    [(_ x) (test-pattern x)]))

(define-syntax-rule (mk-hash (v x) ...)
  (make-immutable-hash (list (cons 'v (test-subs-rhs x)) ...)))

(define (test-plist . elems)
  (plist test-origin (apply list elems)))

(check-equal? (sexpr->pattern '(Cond (^ (^ x y) (^ xs ys) ... (if (^ $else x)))))
  (plist (t-macro 'Cond)
   (list (ellipsis (t-syntax)
                   (list (plist (t-syntax)
                                (list (pvar 'x) (pvar 'y))))
                   (plist (t-syntax)
                          (list (pvar 'xs) (pvar 'ys)))
                   (list (plist (t-apply)
                                (list (pvar 'if)
                                      (plist (t-syntax)
                                             (list (literal '$else) (pvar 'x))))))))))

(define-syntax-rule (test-show ptn str)
  (check-equal? (show-pattern (test-pattern ptn)) str))

(test-show x "x")
(test-show $else "$else")
(test-show c "c")
(test-show 3 "3")
(test-show () "()")
(test-show (x) "(x)")
(test-show (x y) "(x y)")
(test-show (1 x #t y "string") "(1 x #t y \"string\")")
(test-show (M x y ...) "(M x y ...)")
(test-show (x ...) "(x ...)")
(test-show (x y ...) "(x y ...)")
(test-show (x ... y) "(x ... y)")
(test-show (x y x ... y x) "(x y x ... y x)")
(test-show (() (() (x))) "(() (() (x)))")


;;;;;;;;;;;
;; Terms ;;
;;;;;;;;;;;

(check-equal? (term->pattern (term-id (list 'o1 'o2) (term-list (list) (list 1 "two"))))
              (tag (tag (plist (t-apply) (list (constant 1) (constant "two"))) 'o2) 'o1))

(define-syntax-rule (check-term<->pattern p)
  (check-equal? (make-pattern p) (term->pattern (pattern->term (make-pattern p)))))

(define-syntax-rule (check-pattern<->term t)
  (check-equal? (make-term t) (pattern->term (term->pattern (make-term t)))))

(check-term<->pattern (M $x "y" (Q z)))
(check-pattern<->term (M $x y (Q "z")))

;;;;;;;;;;;;;;;;;
;; Unification ;;
;;;;;;;;;;;;;;;;;

(define-syntax-rule (check-unify x y z)
  (check-equal? (unify (test-pattern x) (test-pattern y))
                (test-pattern z)))

(define-syntax-rule (check-unify-fail x y)
  (begin
    (check-exn CantUnify? (thunk (unify (test-pattern x) (test-pattern y))))
    (check-exn CantUnify? (thunk (unify (test-pattern y) (test-pattern x))))))

(check-unify x x x)
(check-unify x y x) ; y is also reasonable
(check-unify x a a)
(check-unify a x a)
(check-unify-fail x $a)
(check-unify x () ())
(check-unify () x ())
(check-unify x (y ...) (y ...))
(check-unify (x ...) y (x ...))
(check-unify a a a)
(check-unify-fail a b)
(check-unify-fail a $a)
(check-unify-fail a ())
(check-unify-fail a (x ...))
(check-unify-fail $a ())
(check-unify-fail $a (x ...))
(check-unify () () ())
(check-unify (a $b c) (a $b c) (a $b c))
(check-unify (x $a b) (a $a y) (a $a b))
(check-unify (x a $c) (y a $c) (x a $c))
(check-unify-fail (a a) (a a a))
(check-unify-fail (x $a b) (a z y))
(check-unify () (x ...) ())
(check-unify (x ...) () ())
(check-unify (x ...) (y ...) (x ...))
(check-unify-fail (a b c d e) (a b x ... d))
(check-unify (a b c d) (a b x ... c d) (a b c d))
(check-unify (a b c d e f) (a b x ... e f) (a b c d e f))
(check-unify-fail (a b c d e f) (a b (x) ... e f))
(check-unify ((a b) (a x) ... (c d)) ((a b) (z y) ...) ((a b) (a x) ... (c d)))
(check-unify ((a b) (z y) ...) ((a b) (a x) ... (c d)) ((a b) (a x) ... (c d)))
(check-unify (a (b b) x ...)   (a (y y) ...)     (a (b b) (y y) ...))
(check-unify (x ... (b b) a)   ((y y) ... a)     ((y y) ... (b b) a))
(check-unify (a b z ...)       (x y ...)         (a b z ...))
(check-unify (z ... a b)       (y ... x)         (z ... a b))
(check-unify (((x a) ...) ...) (((y a) ...) ...) (((x a) ...) ...))
(check-unify (((x a) ...) ...) ((y a) ...)       ())
(check-unify ((x x) ...)       ((a a) y ...)     ((a a) (x x) ...))
(check-unify ((x x) ...)       (y ... (a a))     ((x x) ... (a a)))
(check-unify ((x y) ...)       ((a b) (a c))     ((a b) (a c)))

;;;;;;;;;;;;;;
;; Matching ;;
;;;;;;;;;;;;;;

(define-syntax-rule (check-minus x y z)
  (check-equal? (minus (test-pattern x) (test-pattern y))
                z))

(define-syntax-rule (check-minus-fail x y)
  (check-exn CantMatch? (thunk (minus (test-pattern x) (test-pattern y)))))

(check-minus x x (mk-hash (x x)))
(check-minus x y (mk-hash (y x)))
(check-minus-fail x $a)
(check-minus-fail $a x)
(check-minus a x (mk-hash (x a)))
(check-minus-fail x a)
(check-minus () x (mk-hash (x ())))
(check-minus-fail x ())
(check-minus (y ...) x (mk-hash (x (y ...))))
(check-minus-fail x (y ...))
(check-minus $a $a (mk-hash))
(check-minus-fail $a $b)
(check-minus-fail a $a)
(check-minus-fail $a a)
(check-minus a a (mk-hash))
(check-minus-fail a b)
(check-minus-fail a ())
(check-minus-fail a (x ...))
(check-minus-fail () a)
(check-minus-fail (x ...) a)
(check-minus-fail $a ())
(check-minus-fail $a (x ...))
(check-minus-fail () $a)
(check-minus-fail (x ...) $a)
(check-minus () () (mk-hash)) ; !!!
(check-minus-fail (x ...) ())
(check-minus ()              (x ...) (mk-hash (x (@))))
(check-minus (x ...)         (y ...) (mk-hash (y (@... () x ()))))
(check-minus (a x ... b)     (y ...) (mk-hash (y (@... (a) x (b)))))
(check-minus (a b x ... b c) (y ...) (mk-hash (y (@... (a b) x (b c)))))
(check-minus-fail (x ...) (a y ...))
(check-minus-fail (x ...) (y ... a))
(check-minus-fail (a x ...) (a y ... a))
(check-minus (a (x ...) ...) (y ...) (mk-hash (y (@... (a) (x ...) ()))))


;;;;;;;;;;;;;;;;;;
;; Substitution ;;
;;;;;;;;;;;;;;;;;;


(define-syntax-rule (check-subs-into x y z w)
  (check-equal? (substitute (minus (test-pattern x) (test-pattern y))
                            (test-pattern z))
                (test-pattern w)))

(define-syntax-rule (check-subs x y)
  (check-subs-into x y y x))

(define-syntax-rule (check-unify-subs x y)
  (let ((px (test-pattern x))
        (py (test-pattern y)))
    (let ((pz (unify px py)))
      (check-equal? (substitute (minus pz px) px) pz)
      (check-equal? (substitute (minus pz py) py) pz))))

(check-subs a a)
(check-subs a x)
(check-subs (x ...) (y ...))
(check-subs (a x ... b) (y ...))
(check-subs (a b c) (a x ...))
(check-subs ((x ...) b (y ...)) (z ...))
(check-subs-into (a b c) (x ... y) ((x y) ...) ((a c) (b c)))
(check-subs-into ((x ...) ...) (y ...) (y ...) ((x ...) ...))
(check-unify-subs x a)
(check-unify-subs x ())
(check-unify-subs x (y ...))
(check-unify-subs x ((y ...) ...))
(check-unify-subs (x ...) (y ...))

(check-unify-subs (a (b b) x ...) (a (y y) ...))
(check-unify-subs (x ... (b b) a) ((y y) ... a))
(check-unify-subs (a b z ...) (x y ...))
(check-unify-subs (z ... a b) (y ... x))
(check-unify-subs (((x a) ...) ...) (((y a) ...) ...))
(check-unify-subs (((x a) ...) ...) ((y a) ...))
(check-unify-subs ((x x) ...) ((a a) y ...))
(check-unify-subs ((x x) ...) (y ... (a a)))
(check-unify-subs ((x y) ...) ((a b) (a c)))


;;;;;;;;;;;;;;;;;;
;; Environments ;;
;;;;;;;;;;;;;;;;;;
#|
(check-equal? (hash-union (mk-hash (x a) (y b)) (mk-hash (z c)))
              (mk-hash (x a) (y b) (z c)))

(check-equal? (inter-list-envs (set 'x 'y) (list (mk-hash (x a) (y b))
                                                 (mk-hash (x b) (y c))))
              (make-immutable-hash
               (list (cons 'x (inter-list (list (constant 'a) (constant 'b))))
                     (cons 'y (inter-list (list (constant 'b) (constant 'c)))))))

(check-equal? (free-vars (ellipsis (list (pvar 'x) (literal 'a))
                                     (plist (list (constant 'b) (pvar 'y)))
                                     (list (constant 'c) (pvar 'z) (pvar 'x))))
              (set 'x 'y 'z))

(check-equal? (replace (mk-hash (x y) (y (a)))
                       (test-pattern '((x y) (x a y) ... b z)))
              (test-pattern '((y (a)) (y a (a)) ... b z)))
|#

(check-exn OccursCheck? (thunk (bind 'x (pvar 'x) empty-env)))
(check-exn OccursCheck? (thunk (bind 'x (pvar 'y) (singleton-env 'y (pvar 'x)))))
(check-equal? (bind 'x (test-pattern (y a))
                    (mk-hash (y (a (z else) ...))))
              (mk-hash (x ((a (z else) ...) a))
                       (y (a (z else) ...))))


;;;;;;;;;;;;;
;; Utility ;;
;;;;;;;;;;;;;

(check-equal? (range 3) (list 0 1 2))

(check-eq? (all-eq? (list 1 2 1)) false)
(check-eq? (all-eq? (list 1 1 1)) true)

(check-equal? (compose 1 (list (λ (x) (+ x 1)) (λ (x) (* x 2))))
              4)

(check-equal? (hash-modify (make-immutable-hash '((x . 1) (y . 2))) (λ (x) (+ x 1)))
              (make-immutable-hash '((x . 2) (y . 3))))

(check-equal? (hash-add-bindings (make-immutable-hash '((x . 1) (y . 2)))
                                 '((y . 3) (z . 4)))
              (make-immutable-hash '((x . 1) (y . 3) (z . 4))))

(check-equal? (split-list '... '()) false)
(check-equal? (split-list '... '(a b ... c d)) (cons '(a b) '(c d)))
(check-equal? (split-list '... '(a b c d)) false)

(check-equal? (repeat 3 'a) '(a a a))

(check-equal? (all-distinct-pairs '(1 2 3)) '((1 . 2) (1 . 3) (2 . 3)))

(display "ok\n")

;;;;;;;;;;;;
;; Macros ;;
;;;;;;;;;;;;


(define-macro Cond
  [(_ (^ $else x))    x]
  [(_ (^ x y))       (if x y (void))]
  [(_ (^ x y) z zs ...) (! if x y (Cond z zs ...))])

(define cond-origin* (t-macro 'Cond))
(define (plist* o . xs) (plist o (apply list xs)))

(check-equal? (lookup-macro 'Bob) #f)
(check-equal? (lookup-macro 'Cond)
  (Macro 'Cond
    (list
     (MacroCase (plist* cond-origin*
                        (plist* (t-syntax) (literal '$else) (pvar 'x)))
                (tag (pvar 'x) (o-macro 'Cond 0)))
     (MacroCase (plist* cond-origin*
                        (plist* (t-syntax) (pvar 'x) (pvar 'y)))
                (tag (tag (plist* (t-apply)
                                  (constant 'if) (pvar 'x) (pvar 'y)
                                  (tag (plist* (t-apply) (constant 'void))
                                       (o-branch)))
                          (o-branch))
                     (o-macro 'Cond 1)))
     (MacroCase (ellipsis cond-origin*
                          (list (plist* (t-syntax) (pvar 'x) (pvar 'y)) (pvar 'z))
                          (pvar 'zs)
                          (list))
                (tag (plist* (t-apply) (constant 'if) (pvar 'x) (pvar 'y)
                             (ellipsis cond-origin*
                                       (list (pvar 'z))
                                       (pvar 'zs)
                                       (list)))
                     (o-macro 'Cond 2))))))

(define-syntax-rule (test-expand-unexpand p)
  (check-equal? (unexpand-pattern (expand-pattern (test-pattern p)))
                (test-pattern p)))

(test-expand-unexpand (Cond [^ 1 2]))
(test-expand-unexpand (Cond [^ $else 2]))
(test-expand-unexpand (Cond [^ (+ a 2) 1] [^ $else (+ 1 2)]))
(test-expand-unexpand (Cond [^ $else (+ 1 1)]))
(test-expand-unexpand (Cond [^ (+ a 2) 1] [^ $else 2]))

(define-macro M
  ((M x y ...)
   '((x y) ...)))

(check-equal? (show-term (expand-term (make-term (M (a) b c))))
              "'(((a) b) ((a) c))")

#|
;;;;;;;;;;;;;;
;;; Letrec ;;;
;;;;;;;;;;;;;;

(define-syntax reclet-lets
  (syntax-rules ()
    [(reclet-lets () b) b]
    [(reclet-lets (v vs ...) b)
     (let ((v "gremlin")) (reclet-lets (vs ...) b))]))

(define-syntax reclet-sets
  (syntax-rules ()
    [(reclet-sets () b) b]
    [(reclet-sets ((v x) (vs xs) ...) b)
     (begin (set! v x) (reclet-sets ((vs xs) ...) b))]))

(define-syntax reclet
  (syntax-rules ()
    [(reclet ((v x) ...) b)
     (reclet-lets (v ...) (reclet-sets ((v x) ...) b))]))

(check-equal?
  (reclet ((x 1) (y (+ x 1)) (x 2) (z (+ x y))) (+ x z))
  6)

(check-equal? (reclet ((x x)) x) "gremlin")

(check-equal?
 (let ((x 1)) (reclet ((x 2)) x))
 2)

(check-equal?
 ((λ (x) (reclet ((x 2)) x)) 1)
 2)

(check-equal?
 (reclet ((x 2)) (let ((x 1)) x))
 1)

(check-equal?
 (reclet ((x 1) (y 2))
   (let ((x 3))
     (reclet ((y 4))
             (+ x y))))
 7)

|#

#|
(define (tag-cond2 id e)
  (Tag e id (list-ref (Macro-cases (lookup-macro 'cond)) 1)))

(check-equal?
  (unexpand (tag-cond2 17 (make-plist (tag-cond2 17 (constant 'if))
                                      (tag-cond2 17 (constant 'false))
                                      (tag-cond2 17 (constant 'true))
                                      (tag-cond2 17 (make-plist
                                        (tag-cond2 17 (constant 'void)))))))
  (test-pattern (cond (false true))))

(check-exn NotUnexpandable? (thunk
  (unchecked-unexpand
   (tag-cond2 17 (make-plist (tag-cond2 17 (constant 'if))
                             (tag-cond2 17 (constant 'false))
                             (tag-cond2 18 (constant 'true))
                             (tag-cond2 17 (make-plist
                                            (tag-cond2 17 (constant 'void)))))))))
|#

;(show-pattern (expand-macro (lookup-macro 'cond) (test-pattern (cond (a 1) (else 2)))))
;(show-pattern (expand (test-pattern (cond (a 1) (else 2)))))
;(show-pattern (unexpand (expand (test-pattern (cond (a 1) (else 2))))))
;(show-pattern (expand-macro (lookup-macro 'cond) (test-pattern (cond (false true)))))

