#lang racket

(require "term.rkt")
(require "racket-stepper.rkt")

; See hs/racket.grammar for sugar definitions.

(set-debug-communication! #f)
(set-show-continuations! #t)
(set-hide-external-calls! #f)
(set-debug-steps! #f)


#;(with-resugaring
 
  (test-eval (or (and #t #f) #f))
 
  (test-eval (let [[xor (lambda (x y) (or (and x y) (and (not x) (not y))))]]
               (xor (xor #f #t) (xor #t #f))))
 
  (test-eval (let [[x (+ 1 2)] [y (+ 3 4)]] (+ x y)))
  
  (test-eval (+ 1 (my-external-function (lambda (x) (+ x 1)))))
 
  (test-eval (+ 1 (+ 2 (+ 3 (call/cc (lambda (k) (+ 4 (k (+ 5 6)) (+ 7 8)))) 9)) 10))
  (test-eval (+ 1 (call/cc (lambda (k) (+ 2 (call/cc (lambda (k2) (+ 3 (k 1729)))))))))
  (test-eval (let [[k (call/cc (lambda (c) c))]] (+ 2 (k (lambda (x) 3)))))
  (test-eval (+ 1 (call/cc (lambda (k) (+ 2 (k 3))))))
  (test-eval (call/cc (lambda (k) (k (+ (+ 1 2) (+ 3 4))))))
  (test-eval ((call/cc call/cc) (lambda (x) 3)))
 ;(test-eval ((call/cc call/cc) (call/cc call/cc))) ;-- loops
)

(with-resugaring
 (test-eval ((function (x) (+ 1 (return (+ x 2)))) (+ 3 4)))
 (test-eval ((function (f) (+ 1 (return (f 2))))
             (function (x) (+ 3 (return (+ x 4))))))
)