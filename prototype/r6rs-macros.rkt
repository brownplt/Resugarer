#lang racket

(require "resugar.rkt")
(require "resugar-racket.rkt")

; All macros defined in R6RS

; Translatable (7/9):
;   Let And Or Letrec Cond Let* Letrec*
; Not translatable (1/9):
;   Let-values
; Translatable, but stepper doesn't support (1/9):
;   Case

; NOT DISJOINT!
(define-macro Let
  ((Let (^ (^ name val) ...) body1 body2 ...)
   ((lambda (name ...) body1 body2 ...)
    val ...)))
;  ((Let tag ((name val) ...) body1 body2 ...)
;   ((Letrec ((tag (lambda (name ...)
;                    body1 body2 ...)))
;            tag)
;    val ...))))

; ALMOST DISJOINT
(define-macro And
  ((And) #t)
  ((And test) test)
  ((And test1 test2 tests ...)
   (if test1 (! And test2 tests ...) #f)))

; ALMOST DISJOINT
(define-macro Or
  ((Or) #f)
  ((Or test) test)
  ((Or test1 test2 tests ...)
   (Let (^ (^ x test1))
        (if x x (! Or test2 tests ...)))))

; ALMOST DISJOINT
(define-macro Case
  ((Case expr0
     (^ (^ key ...) res1 res2 ...)
     ...
     (^ $else else-res1 else-res2 ...))
   (Let (^ (^ tmp expr0))
        (Cond
          (^ (memv tmp ’(key ...)) res1 res2 ...)
          ...
          ($else else-res1 else-res2 ...))))
  ((Case expr0
     (^ (^ keya ...) res1a res2a ...)
     ;((keyb ...) res1b res2b ...)
     ...)
   (Let (^ (^ tmp expr0))
        (Cond
          (^ (memv tmp ’(keya ...)) res1a res2a ...)
          ;(^ (memv tmp ’(keyb ...)) res1b res2b ...)
          ...))))

; ALMOST DISJOINT
(define-macro Letrec
  ((Letrec (^) body1 body2 ...)
   (Let (^) body1 body2 ...))
  ((Letrec (^ (^ var init) (^ vars inits) ...) body1 body2 ...)
   (Letrec-helper
    (^ var vars ...)
    (^)
    (^ (^ var init) (^ vars inits) ...)
    body1 body2 ...)))

; DISJOINT?
(define-macro Cond
  ((Cond (^ $else result1 result2 ...))
   (begin result1 result2 ...))
  ((Cond (^ test $=> result))
   (Let ((temp test))
        (if temp (result temp))))
  ((Cond (^ test $=> result) clause1 clause2 ...)
   (Let ((temp test))
        (if temp
            (result temp)
            (Cond clause1 clause2 ...))))
  ((Cond (^ test)) test)
  ((Cond (^ test) clause1 clause2 ...)
   (Let (^ (^ temp test))
        (if temp
            temp
            (Cond clause1 clause2 ...))))
  ((Cond (^ test result1 result2 ...))
   (if test (begin result1 result2 ...)))
  ((Cond (^ test result1 result2 ...)
         clause1 clause2 ...)
   (if test
       (begin result1 result2 ...)
       (Cond clause1 clause2 ...))))

; DISJOINT
(define-macro Let*
  ((Let* (^) body1 body2 ...)
   (Let (^) body1 body2 ...))
  ((Let* (^ (^ name1 expr1) (^ name2 expr2) ...)
         body1 body2 ...)
   (Let (^ (^ name1 expr1))
        (Let* (^ (^ name2 expr2) ...)
              body1 body2 ...))))

; DISJOINT
(define-macro Letrec-helper
  ((Letrec-helper
    (^)
    (^ temp ...)
    (^ (^ var init) ...)
    body1 body2 ...)
   (Let (^ (^ var (void)) ...)
        (Let (^ (^ temp init) ...)
             (set! var temp)
             ...)
        (Let (^) body1 body2 ...)))
  ((Letrec-helper
    (^ x y ...)
    (^ temp ...)
    (^ (^ var init) ...)
    body1 body2 ...)
   (Letrec-helper
    (^ y ...)
    (^ magic-gensym temp ...) ; magic-gensym should be newtemp -- hygene problem
    (^ (^ var init) ...)
    body1 body2 ...)))

; DISJOINT
(define-macro Letrec*
  ((Letrec* (^ (^ var1 init1) ...) body1 body2 ...)
   (Let (^ (^ var1 (void)) ...)
        (set! var1 init1)
        ...
        (Let (^) body1 body2 ...))))

#|
; DISJOINT
(define-macro Let-values
  ((Let-values (^ binding ...) body1 body2 ...)
   (Let-values-helper1
    (^)
    (^ binding ...)
    body1 body2 ...)))

; DISJOINT
(define-macro Let-values-helper1
  ;; map over the bindings
  ((Let-values
    (^ (^ id temp) ...)
    (^)
    body1 body2 ...)
   (Let (^ (^ id temp) ...) body1 body2 ...))
  ((Let-values
    assocs
    (^ (^ formals1 expr1) (^ formals2 expr2) ...)
    body1 body2 ...)
   (Let-values-helper2
    formals1
    (^)
    expr1
    assocs
    (^ (^ formals2 expr2) ...)
    body1 body2 ...)))

; TRICKY!!!
(define-macro Let-values-helper2
  ;; create temporaries for the formals
  ((Let-values-helper2
    (^)
    temp-formals
    expr1
    assocs
    bindings
    body1 body2 ...)
   (call-with-values
    (lambda () expr1)
    (lambda temp-formals
      (Let-values-helper1
       assocs
       bindings
       body1 body2 ...))))
  ((Let-values-helper2
    (^ first rest ...)
    (^ temp ...)
    expr1
    (^ assoc ...)
    bindings
    body1 body2 ...)
   (Let-values-helper2
    (^ rest ...)
    (^ temp ... newtemp)
    expr1
    (^ assoc ... (first newtemp))
    bindings
    body1 body2 ...))
  ((Let-values-helper2
    rest-formal
    (^ temp ...)
    expr1
    (^ assoc ...)
    bindings
    body1 body2 ...)
   (call-with-values
    (lambda () expr1)
    (lambda (temp ... . newtemp)
      (Let-values-helper1
       (^ assoc ... (rest-formal newtemp))
       bindings
       body1 body2 ...)))))

(set-debug-steps! #f)

; DISJOINT
(define-macro Let*-values
  ((Let*-values (^) body1 body2 ...)
   (Let (^) body1 body2 ...))
  ((Let*-values (^ binding1 binding2 ...)
                body1 body2 ...)
   (Let-values (^ binding1)
               (Let*-values (^ binding2 ...)
                            body1 body2 ...))))
|#

; Illustrates the problem with Case: the stepper doesn't support quotation.
(define-macro Q
  [(Q x) 'x])

(test-eval (Let [^ [^ x 1]] x))
(test-eval (Letrec (^) 3))
(test-eval (Letrec [^ [^ x 1]] x))
(test-eval (Let [^ [^ x 3]] x))
(test-eval (Let [^ [^ x 1] [^ y (+ 1 2)]] (+ x y)))
(test-eval (And #t #t #f #t))
(test-eval (Or #f #f #t #f))
(test-eval (Letrec [^ [^ x 1] [^ y 2]] (+ x y)))
(test-eval (Letrec (^ [^ is-even? (lambda (n) (Or (zero? n) (is-odd? (sub1 n))))]
                      [^ is-odd? (lambda (n) (And (not (zero? n)) (is-even? (sub1 n))))])
                   (cons (is-even? 11) (is-odd? 11))))
(test-eval (Let* [^ [^ x 1] [^ y x]] (+ x y)))
(test-eval (Letrec* [^ [^ x 1] [^ y x]] (+ x y)))
; The following fail:
;(test-eval (Q 3))
;(test-eval (Case (* 2 3) (^ (^ 2 3 5 7) 'prime) (^ (^ 1 4 6 8 9) 'composite)))