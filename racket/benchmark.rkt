#lang racket

(require "term.rkt")
(require "racket-stepper.rkt")
(require profile)

(set-silence! #t)

(define-syntax-rule
  (run-tests expr ...)
  (begin
    (display "\nWITH RESUGARING:\n")
    (with-resugaring expr ...)
    (display "\nWITHOUT RESUGARING:\n")
    (without-resugaring expr ...)))

(run-tests
 (display "\nBig-stack factorial:")
 (time (test-eval (define (factorial n)
                    (if (eq? n 0)
                        1
                        (* n (factorial (- n 1)))))
                  (factorial 10000)
                  "ok"))
 (display "\nSmall-stack factorial:")
 (time (test-eval (define (factorial n acc)
                    (if (eq? n 0)
                        acc
                        (factorial (- n 1) (* n acc))))
                  (factorial 10000 1)
                  "ok"))
)
