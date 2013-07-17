#lang racket

(require profile)
(require "resugar.rkt")
(require "resugar-racket.rkt")

  (define-macro Cond
    [(Cond [^ $else x])   (begin x)]
    [(Cond [^ x y])       (if x y (void))]
    [(Cond [^ x y] z zs ...) (if x y (! Cond z zs ...))])
  
  (define-macro Let
    [(Let [^ [^ x e]] b)
     ((lambda (x) b) e)]
    [(Let [^ [^ x e] y ys ...] b)
     ((lambda (x) (! Let [^ y ys ...] b)) e)])
  
  (define-macro Let1
    [(Let1 v x y)
     (Let [^ [^ v x]] y)])
  
  (define-macro Set
    [(Set [^ [^ x e]] b)
     (begin (set! x e) b)]
    [(Set [^ [^ x e] y ys ...] b)
     (begin (set! x e) (! Set [^ y ys ...] b))])

  (define-macro Letrec
    [(Letrec [^ [^ x e] ...] b)
     (Let [^ [^ x (void)] ...]
          (Set [^ [^ x e] ...]
               b))])
  
  (define-macro Or
    [(Or x) (begin x)]
    [(Or x y ys ...)
     (Let [^ [^ t x]] (if t t (! Or y ys ...)))])
  
  (define-macro Or2
    [(Or2 x y) (Let1 t x (if t t y))])
  
  (define-macro And
    [(And x) (begin x)]
    [(And x y ys ...)
     (if x (! And y ys ...) #f)])
  
  ; Not well-formed:
  ;(define-macro Quickand
  ;  [(Quickand x #t) x]
  ;  [(Quickand #t y) y])
  
  (define-macro Just
    [(Just x) (begin x)])
  
  (define-macro M1
    [(M1 $emm) 3])
  
  (define-macro M2
    [(M2 x) (M1 x)])
  
  (define-macro Inc
    [(Inc x) (+ x 1)])
  
  (define-macro Inc2
    [(Inc2 x) (+ 1 (Inc x))])
  
  (define-macro Cdavr
    [(Cdavr input)
     (Letrec [^ [^ init (λ (x)
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "c" head) (! more tail)]
                                  [^ $else (begin #f)]))))]
                [^ more (λ (x)
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "a" head) (! more tail)]
                                  [^ (equal? "d" head) (! more tail)]
                                  [^ (equal? "r" head) (! end tail)]
                                  [^ $else (begin #f)]))))]
                [^ end (λ (x)
                   (equal? x ""))]]
             (! init input))])
  
  (define-macro ProcessState
    [(_ "accept")
     (lambda (stream)
       (Cond
        [^ (equal? "" stream) #t]
        [^ $else #f]))]
    [(_ [^ label $-> target] ...)
     (lambda (stream)
       (if (equal? "" stream) #f
           (Let [^ [^ head (string-first stream)]
                   [^ tail (string-rest stream)]]
                (Cond
                 [^ (equal? label head) (! target tail)]
                 ...
                 [^ $else (begin #f)]))))])

  (define-macro Automaton
    [(_ init-state
        [^ state $: response ...]
        ...)
     (Letrec [^ [^ state (ProcessState response ...)] ...]
             (λ (x) (! init-state x)))]) ; if just init-state, you don't see the application (init-state input)
  
  (define (time-fib)
    (display "Fibonacci:\n")
    (time (letrec ((fib (λ (n) (if (or (eq? n 0) (eq? n 1))
                                   1
                                   (+ (fib (- n 1)) (fib (- n 2)))))))
            (begin (fib 20) (void))))
    (time (test-silent-eval (Letrec [^ [^ fib (λ (n) (if (Or (eq? n 0) (eq? n 1))
                                                  1
                                                  (+ (fib (- n 1)) (fib (- n 2)))))]]
                             (begin (fib 20) (void))))))
  
  (define (time-factorial)
    (display "Factorial:\n")
    (time (letrec ((factorial (λ (n) (if (eq? n 0)
                                         1
                                         (* n (factorial (- n 1)))))))
            (begin (factorial 10000) (void))))
    (time (test-silent-eval (Letrec [^ [^ factorial (λ (n) (if (eq? n 0)
                                                       1
                                                       (* n (factorial (- n 1)))))]]
                             (begin (factorial 10000) (void))))))
  
  (define (time-fast-factorial)
    (display "Accumulating Factorial:\n")
    (time (letrec ((factorial (λ (n prod)
                                (if (eq? n 0) prod
                                    (factorial (- n 1) (* n prod))))))
            (begin (factorial 10000 1) (void))))
    (time (test-silent-eval (Letrec [^ [^ factorial (λ (n prod)
                                   (if (eq? n 0) prod (factorial (- n 1) (* n prod))))]]
                             (begin (factorial 10000 1) (void))))))
  
  (set-debug-steps! #f)
  (set-debug-tags! #f)
  (set-debug-vars! #f)
  (set-hide-external-calls! #f)
  
  (test-eval 3)
  (test-eval (+ 1 2))
  (test-eval (+ (+ 1 2) 4))
  (test-eval (+ 1 (+ 2 4)))
  (test-eval (+ (+ 1 2) (+ 3 4)))
  (test-eval (if #t (+ 1 2) (+ 3 4)))
  (test-eval (if (+ 1 2) (+ 3 4) (+ 5 6)))
  (test-eval (λ (x) x))
  (test-eval ((λ (x) (+ x 1)) 3))
  (test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
  (test-eval (+ 1 (my-external-function (λ (x) (+ x 1)))))
  (test-eval (+ 0 (car (cons (+ 1 2) (+ 3 4)))))
  (test-eval (Or 1 2))
  (test-eval (Or (And #f #t) (+ 1 2)))
  (test-eval (Inc (+ 1 2)))
  (test-eval (+ 1 (begin (begin (+ 1 2)))))
  (test-eval (begin (+ 1 2) (+ 3 4)))
  (test-eval (Inc (+ (Inc 1) (Inc 2))))
  (test-eval (+ 1 (Cond [^ #f (+ 1 2)] [^ (Or #f #t) (+ 2 3)])))
  (test-eval ((λ (x) (if (set! x (+ x 1)) (cons x x) x)) 3))
  (test-eval ((λ (x) (begin (set! x (+ x 1)) (+ x 1))) 3))
  (test-eval (Let [^ [^ x 1]] x))
  (test-eval (Letrec [^ [^ x 1]] x))
  (test-eval (Just (+ 1 2)))
  (test-eval (Let1 x 3 x))
  (test-eval (Let [^ [^ x 3]] x))
  (test-eval (Let [^ [^ x 1] [^ y (+ 1 2)]] (+ x y)))
  (test-eval (Letrec [^ [^ f (λ (n) (g n))] [^ g (λ (n) (+ n 1))]] (f 3)))
  (test-eval (Or (zero? 3) (sub1 3)))
  (test-eval (And (not (zero? 3)) (sub1 3)))
  (test-eval (! + 1 2))
  (test-eval (Letrec [^ [^ f (λ (n) (if (zero? n) 77 (f (! + 0 0))))]] (f (+ 1 2))))
  
  (test-eval (Letrec [^ [^ is-even? (λ (n) (Or (zero? n) (is-odd? (sub1 n))))]
                        [^ is-odd? (λ (n) (And (not (zero? n)) (is-even? (sub1 n))))]]
                     (is-odd? 11)))
  (test-eval (Let [^ [^ f (λ (x) (+ x 1))]] (f 3)))
  (test-eval (begin (+ 1 2) (+ 3 4)))
  (test-eval ((λ (f) (begin (set! f (λ (x) x)) (f 4))) 3))
  
  (test-eval (Cdavr "cdad"))
  (test-eval (Cdavr "cadr"))
  ;(test-expand-term (Cdavr "cadr")) ; Huge!
  ; You see (m "cadr") instead of (init "cadr") for the same reason
  ;   (Let [[x (λ (v) v)]] (Let [[y x]] (Let [[z y]] (z 0))))
  ; steps through (z 0) -> ((λ (v) v) 0) -> 0
  ; instead of    (z 0) -> (y 0) -> (x 0) -> ((λ (v) v) 0) -> 0
  ; steps through (+ 1 2), but never through (+ (+ 0 1) 2).
  (test-eval ((Automaton
                 init
                 [^ init $: [^ "c" $-> more]]
                 [^ more $: [^ "a" $-> more]
                            [^ "d" $-> more]
                            [^ "r" $-> end]]
                 [^ end $:  "accept"])
              "cadr"))
  (test-eval ((Automaton
                 init
                 [^ init $: [^ "c" $-> more]]
                 [^ more $: [^ "a" $-> more]
                            [^ "d" $-> more]
                            [^ "r" $-> end]]
                 [^ end $:  "accept"])
              "cdad"))
  (test-eval ((Automaton
                 init
                 [^ init   $: [^ "1" $-> more-1]]
                 [^ more-1 $: [^ "0" $-> more-0]
                              [^ "1" $-> more-1]
                              [^ "." $-> end]]
                 [^ more-0 $: [^ "0" $-> more-0]
                              [^ "1" $-> more-1]]
                 [^ end    $: "accept"])
              "1101."))
  
  (show-term (expand-term (make-term (Letrec [^ [^ fib (λ (n) (if (Or (eq? n 0) (eq? n 1))
                                                  1
                                                  (+ (fib (- n 1)) (fib (- n 2)))))]]
                             (begin (fib 20) (void))))))
  
  (test-term (Letrec [^ [^ fib (λ (n) (if (Or (eq? n 0) (eq? n 1))
                                                  1
                                                  (+ (fib (- n 1)) (fib (- n 2)))))]]
                             (begin (fib 20) (void))))
  
  (time-fast-factorial)
  (time-fib)
  (time-factorial)

  ; Racket profiler totally unhelpful within eval
  #;(profile-silent-eval
    (Letrec [^ [^ fib (λ (n) (if (Or (eq? n 0) (eq? n 1))
                                 1
                                 (+ (fib (- n 1)) (fib (- n 2)))))]]
            (fib 20)))
  #|
  (test-expand-term (Let [^ [^ x 1]] (+ x 1)))
  
  (test-expand-term (Letrec [^ [^ [^ fib n] (if (Or (eq? n 0) (eq? n 1))
                                               1
                                               (+ (fib (- n 1)) (fib (- n 2))))]]
                           (fib 15)))
|#
  ;(test-eval (M2 $emm)) BUG! I don't know how to fix this w/o ugly hacks
  #|
  (time (test-eval (Letrec [^ [^ [^ fib n]
                                 (if (Or (eq? n 0) (eq? n 1)) 1 (+ (fib (- n 1)) (fib (- n 2))))]]
                           (fib 25))))
  (time (letrec ((fib (λ (n) (if (or (eq? n 0) (eq? n 1)) 1 (+ (fib (- n 1)) (fib (- n 2)))))))
          (fib 25)))
  ;(test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
  ;(test-eval ((lambda (s) (Let [^ [^ x (string-first s)] [^ y (string-rest s)]] y)) "abc"))
  ;(test-eval ((λ (x) (x x)) (λ (x) x)))
|#