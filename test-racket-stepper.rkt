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
      (let [[exp (λ (t)
               (send-command (format "desugar ~a\n" (show-term t)) out)
               (receive-response in err))]
            [unexp (λ (t)
               (send-command (format "resugar ~a\n" (show-term t)) out)
               (receive-response in err))]]
        (parameterize [[expand exp]
                       [unexpand unexp]]
          expr ...
          (subprocess-kill resugarer #t))))))

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
  
  (test-eval (inc 3))
  (test-eval (incinc 3))
  (test-eval (inc (inc 3)))
  (test-eval (inc (inc (inc 3))))
  (test-eval (begin (+ 1 2) (+ 2 3) (+ 3 4)))
  (test-eval (let [[x 1]] (+ 1 2)))
  (test-eval (let [[x (+ 1 2)]] (+ x 3)))
  (test-eval (let [[x 1] [y 2]] 3))
  (test-eval (let [[x (+ 1 2)] [y (+ 3 4)]] (+ x y)))
)
