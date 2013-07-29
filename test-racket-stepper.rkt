#lang racket

(require "utility.rkt")
(require "term.rkt")
(require "racket-stepper.rkt")

(define-syntax-rule (with-resugaring expr ...)
  (begin
    (current-locale "en_US.UTF-8") ; How to make Racket read in unicode?
    (let-values [[(resugarer in out err)
                  (subprocess #f #f #f "hs/Resugarer" "hs/racket.grammar")]]
      (parameterize [[expand
                      (λ (t) (send-command (format "desugar ~a\n" (show-term t)) out)
                        (receive-response in err))]
                     [unexpand
                      (λ (t) (send-command (format "resugar ~a\n" (show-term t)) out)
                        (receive-response in err))]]
        expr ...
        (subprocess-kill resugarer #t)))))

(define-syntax-rule (without-resugaring expr ...)
  (parameterize [[expand (λ (t) t)]
                 [unexpand (λ (t) t)]]
    expr ...))

(set-debug-communication! #t)

(without-resugaring
 (test-eval "blah")
 (test-eval (lambda (x) x))
 (test-eval (+ (+ 1 2) 3))
 (test-eval (+ 1 (+ 2 3)))
 (test-eval ((lambda (x) (+ x 1)) (+ 1 2)))
 (test-eval ((lambda (x) (begin x)) 1)))

(with-resugaring
 (test-eval "blah")
 (test-eval (lambda (x) x))
 (test-eval 3)
 (test-eval (+ 1 2))
 (test-eval (+ (+ 1 2) (+ 3 4)))
 (test-eval ((lambda (x) (+ x 1)) (+ 1 2)))
 (test-eval (let [] 3))
 (test-eval (let [[x 1]] 2))
 (test-eval (let [[x 1]] x))
)
