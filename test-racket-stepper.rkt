#lang racket

(require "term.rkt")
(require "racket-stepper.rkt")

(set-debug-communication! #f)
(set-debug-steps! #f)

(without-resugaring
 (test-eval "blah")
 (test-eval (lambda (x) x))
 (test-eval (+ (+ 1 2) 3))
 (test-eval (+ 1 (+ 2 3)))
 (test-eval ((lambda (x) (+ x 1)) (+ 1 2)))
 (test-eval ((lambda (x) (begin x)) 1))
 (test-eval ((lambda (x) (if (set! x (+ x 1)) (cons x x) x)) 3)))

(with-resugaring
 (test-eval "blah")
 (test-eval (lambda (x) x))
 (test-eval 3)
 (test-eval (+ 1 2))
 (test-eval (+ (+ 1 2) (+ 3 4)))
 (test-eval ((lambda (x) (+ x 1)) (+ 1 2)))
 
  (test-eval 3)
  (test-eval (+ 1 2))
  (test-eval (+ (+ 1 2) 4))
  (test-eval (+ 1 (+ 2 4)))
  (test-eval (+ (+ 1 2) (+ 3 4)))
  (test-eval (if #t (+ 1 2) (+ 3 4)))
  (test-eval (if (+ 1 2) (+ 3 4) (+ 5 6)))
  (test-eval (lambda (x) x))
  (test-eval ((lambda (x) (+ x 1)) 3))
  (test-eval (((lambda (f) (lambda (x) (f (f x)))) (lambda (x) (+ x 1))) (+ 2 3)))
  (test-eval (+ 1 (my-external-function (lambda (x) (+ x 1)))))
  (test-eval (cons 3 7))
  (test-eval (+ 0 (car (cons (+ 1 2) (+ 3 4)))))
  (test-eval (+ 1 (begin (begin (+ 1 2)))))
  (test-eval (begin (+ 1 2) (+ 3 4)))
  (test-eval ((lambda (x) (if (set! x (+ x 1)) (cons x x) x)) 3))
  (test-eval ((lambda (x) (begin (set! x (+ x 1)) (+ x 1))) 3))
  (test-eval ((lambda (f) (begin (set! f (lambda (x) x)) (f 4))) 3))
  
  (test-eval (inc 3))
  (test-eval (inc (inc 3)))
  (test-eval (inc (inc (inc 3))))
  (test-eval (begin (+ 1 2) (+ 2 3) (+ 3 4)))
  (test-eval (let [[x 1]] (+ 1 2)))
  (test-eval (let [[x (+ 1 2)]] (+ x 3)))
  (test-eval (let [[x 1] [y 2]] 3))
  (test-eval (let [[x (+ 1 2)] [y (+ 3 4)]] (+ x y)))
  (test-eval (or 1))
  (test-eval (or 1 2))
  (test-eval (or (or #f #f) (or #f #t) (or #t #f)))
  (test-eval (or (zero? 3) (sub1 3)))
  (test-eval (and (not (zero? 3)) (sub1 3)))
  (test-eval (cond [else 3]))
  (test-eval (cond [#f 1] [else 2]))
  (test-eval (cond [#f 1] [(+ 1 2) (+ 3 4)] [else 7]))
  (test-eval (+ 1 (cond [#f (+ 1 2)] [(or #f #t) (+ 2 3)] [else #f])))
  (test-eval (letrec [[x 1] [y 2]] (+ x y)))
  (test-eval (letrec [[f (lambda (n) (g n))] [g (lambda (n) (+ n 1))]] (f 3)))
  ; BUG:
  #;(test-eval (letrec [[double (lambda (n) (if (zero? n) 0 (+ 2 (double (- n 1)))))]] (double 3)))
  ; BUG:
  #;(test-eval (letrec [[is-even? (lambda (n)
                        (or (zero? n) (is-odd? (sub1 n))))]
                      [is-odd? (lambda (n)
                        (and (not (zero? n)) (is-even? (sub1 n))))]]
                     (is-odd? 11)))
  #;(test-eval ((automaton init [init : accept]) "a"))
  
  #;(test-eval (let [[a (automaton
                       init
                       [init : ["c" -> more]]
                       [more : ["a" -> more]
                               ["d" -> more]
                               ["r" -> end]]
                       [end : accept])]]
               (list (a "cadr")
                     (a "cddr")
                     (a "card"))))
  
  (test-eval (+ 1 (call/cc (λ (k) (k 2)))))
  (test-eval (+ 1 (+ 2 (+ 3 (call/cc (λ (k) (+ 4 (k (+ 5 6)) (+ 7 8)))) 9)) 10))
  (test-eval (+ 1 (call/cc (lambda (k) (+ 2 (call/cc (lambda (k2) (+ 3 (k 1729)))))))))
  (test-eval (Let [^ [^ k (call/cc (lambda (c) c))]] (+ 2 (k (λ (x) 3)))))
  (test-eval (+ 1 (call/cc (λ (k) (+ 2 (k 3))))))
  (test-eval (call/cc (λ (k) (k (+ (+ 1 2) (+ 3 4))))))
  ;(test-eval ((call/cc call/cc) (call/cc call/cc))) ;-- loops
  (test-eval ((call/cc call/cc) (λ (x) 3)))
)
