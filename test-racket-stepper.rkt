#lang racket

(require "utility.rkt")
(require "data.rkt")
(require "term.rkt")
(require "racket-stepper.rkt")

(define (send-command cmd out)
  (when DEBUG_COMMUNICATION (display cmd))
  (display cmd out)
  (flush-output out))
  
(define (read-port port [str ""])
  (let [[line (read-line port)]]
    (if (eof-object? line)
        str
        (read-port port (string-append str line)))))
  
(define (receive-response in err)
  (let [[response (read-line in)]]
    (when DEBUG_COMMUNICATION (display response) (newline))
    (cond [(eof-object? response)
           (display (read-port err)) (newline)
           (fail "Received EOF")]
          [(strip-prefix "success: " response)
           => (λ (t) (term->sexpr (read-term t)))]
          [(strip-prefix "failure: " response)
           => (λ (_) (CouldNotUnexpand))]
          [(strip-prefix "error: " response)
           => (λ (msg) (fail msg))])))

(define-syntax-rule (with-resugaring expr ...)
  (begin
    (current-locale "en_US.UTF-8") ; How to make Racket read in unicode?
    (let-values [[(resugarer in out err)
                  (subprocess #f #f #f "hs/Resugarer" "hs/racket.grammar")]]
      (parameterize
          [[expand (λ (t)
             (send-command (format "desugar ~a\n" (show-term t)) out)
             (receive-response in err))]
           [unexpand (λ (t)
             (send-command (format "resugar ~a\n" (show-term t)) out)
             (receive-response in err))]]
        (let [[result (begin expr ...)]]
          (subprocess-kill resugarer #t)
          result)))))

(define-syntax-rule (without-resugaring expr ...)
  (parameterize [[expand (λ (t) t)]
                 [unexpand (λ (t) t)]]
    expr ...))

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
  (test-eval (letrec [[double (lambda (n) (if (zero? n) 0 (+ 2 (double (- n 1)))))]] (double 3)))
  #|
  (test-eval (letrec [[is-even? (lambda (n)
                        (or (zero? n) (is-odd? (sub1 n))))]
                      [is-odd? (lambda (n)
                        (and (not (zero? n)) (is-even? (sub1 n))))]]
                     (is-odd? 11)))
|#
  (test-eval ((automaton init [init : accept]) "a"))
  
  (test-eval (let [[a (automaton
                       init
                       [init : ["c" -> more]]
                       [more : ["a" -> more]
                               ["d" -> more]
                               ["r" -> end]]
                       [end : accept])]]
               (list (a "cadr")
                     (a "cddr")
                     (a "card"))))
)
