#lang racket
(require rackunit)
(require "utility.rkt")
(require "pattern.rkt")
(require "macro.rkt")


;;;;;;;;;;;;
;; Syntax ;;
;;;;;;;;;;;;

(define test-lits '(else A B C))
(define test-macs '(cond and))
(define test-vars '(x y z xs ys zs))

(define (make-pattern p lits vars)
    (let ((make-pattern (λ (p) (make-pattern p lits vars))))
      (cond [(symbol? p)
             (if (member p lits) (literal p)
                 (if (member p vars) (pvar p)
                     (constant p)))]
            [(list? p)
             (match p
               [(list ps ... q '... rs ...) ; (P1 ... Pn Q*)
                (let ((l (map make-pattern ps))
                      (m (make-pattern q))
                      (r (map make-pattern rs)))
                  (ellipsis l m r))]
               [_ ; (P1 ... Pn)
                (plist (map make-pattern p))])]
            [(or (number? p) (boolean? p))
             (constant p)]
            [else (error (format "bad pattern: ~a" p))])))

(define test-origin (list))

(define-syntax-rule (test-pattern p)
  (sexpr->pattern 'p test-lits test-macs test-vars))

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

(check-equal? (sexpr->pattern '(cond (^ (^ x y) (^ xs ys) ... (if (^ else x))))
                              '(else)
                              '(cond)
                              #f)
  (plist (t-macro 'cond)
   (list (ellipsis (t-syntax)
                   (list (plist (t-syntax)
                                (list (pvar 'x) (pvar 'y))))
                   (plist (t-syntax)
                          (list (pvar 'xs) (pvar 'ys)))
                   (list (plist (t-apply)
                                (list (pvar 'if)
                                      (plist (t-syntax)
                                             (list (literal 'else) (pvar 'x))))))))))

(define-syntax-rule (test-show ptn str)
  (check-equal? (show-pattern (test-pattern ptn)) str))

(test-show x "x")
(test-show else ":else")
(test-show a "'a")
(test-show () "()")
(test-show (x) "(x)")
(test-show (x y) "(x y)")
(test-show (a x b) "('a x 'b)")
(test-show (x ...) "(x ...)")
(test-show (x y ...) "(x y ...)")
(test-show (x ... y) "(x ... y)")
(test-show (x y x ... y x) "(x y x ... y x)")
(test-show (() (() (x))) "(() (() (x)))")


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
(check-unify-fail x A)
(check-unify x () ())
(check-unify () x ())
(check-unify x (y ...) (y ...))
(check-unify (x ...) y (x ...))
(check-unify a a a)
(check-unify-fail a b)
(check-unify-fail a A)
(check-unify-fail a ())
(check-unify-fail a (x ...))
(check-unify-fail A ())
(check-unify-fail A (x ...))
(check-unify () () ())
(check-unify (a B c) (a B c) (a B c))
(check-unify (x A b) (a A y) (a A b))
(check-unify (x a C) (y a C) (x a C))
(check-unify-fail (a a) (a a a))
(check-unify-fail (x A b) (a z y))
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
(check-minus-fail x A)
(check-minus-fail A x)
(check-minus a x (mk-hash (x a)))
(check-minus-fail x a)
(check-minus () x (mk-hash (x ())))
(check-minus-fail x ())
(check-minus (y ...) x (mk-hash (x (y ...))))
(check-minus-fail x (y ...))
(check-minus A A (mk-hash))
(check-minus-fail A B)
(check-minus-fail a A)
(check-minus-fail A a)
(check-minus a a (mk-hash))
(check-minus-fail a b)
(check-minus-fail a ())
(check-minus-fail a (x ...))
(check-minus-fail () a)
(check-minus-fail (x ...) a)
(check-minus-fail A ())
(check-minus-fail A (x ...))
(check-minus-fail () A)
(check-minus-fail (x ...) A)
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

(display "ok\n")

;;;;;;;;;;;;
;; Macros ;;
;;;;;;;;;;;;


(define-macro cond (else) ()
  [(_ (^ else x))    x]
  [(_ (^ x y))       (if x y (void))]
  [(_ (^ x y) z ...) (if x y (cond z ...))])

(define cond-origin* (t-macro 'cond))
(define (plist* o . xs) (plist o (apply list xs)))

(check-equal? (lookup-macro 'bob) #f)
(check-equal? (lookup-macro 'cond)
  (Macro 'cond
    (list
     (MacroCase (plist* cond-origin*
                        (plist* (t-syntax) (literal 'else) (pvar 'x)))
                (pvar 'x))
                ;(plist* (t-apply) (constant '+) (pvar 'x) (constant 0)))
     (MacroCase (plist* cond-origin*
                        (plist* (t-syntax) (pvar 'x) (pvar 'y)))
                (plist* (t-apply)
                        (constant 'if) (pvar 'x) (pvar 'y)
                        (plist* (t-apply) (constant 'void))))
     (MacroCase (ellipsis cond-origin*
                          (list (plist* (t-syntax) (pvar 'x) (pvar 'y)))
                          (pvar 'z)
                          (list))
                (plist* (t-apply) (constant 'if) (pvar 'x) (pvar 'y)
                        (ellipsis cond-origin*
                                  (list)
                                  (pvar 'z)
                                  (list)))))))

(show-pattern (expand (test-pattern (cond (^ (+ a 2) 1) (^ else 2)))))

(show-pattern (unexpand (expand (test-pattern (cond (^ 1 2))))))

(show-pattern (expand (test-pattern (cond (^ 1 2)))))

(check-equal? (unexpand (expand (test-pattern (cond (^ 1 2)))))
              (test-pattern (cond (^ 1 2))))

(check-equal? (unexpand (expand (test-pattern (cond (^ else 2)))))
              (test-pattern (cond (^ else 2))))

(check-equal? (unexpand (expand (test-pattern (cond (^ (+ a 2) 1) (^ else (+ 1 2))))))
              (test-pattern (cond (^ (+ a 2) 1) (^ else (+ 1 2)))))

(expand (test-pattern (cond (^ else 2))))

;(check-equal? (unexpand (expand (test-pattern (cond (^ else (+ 1 1))))))
;              (test-pattern (cond (^ else (+ 1 1)))))

;(check-equal? (unchecked-unexpand (expand (test-pattern (cond ((+ a 2) 1) (else 2)))))
;              (test-pattern (cond ((+ a 2) 1) (else 2))))

(show-pattern (expand (test-pattern (cond (^ (+ a 2) 1) (^ else 2)))))

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
