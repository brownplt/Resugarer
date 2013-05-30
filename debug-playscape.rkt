#lang racket
(require "resugar.rkt")

(define stack (list))

(define (display-stack)
  (display "STACK:\n")
  (map (lambda (x) (display (format "\t~a\n" x))) stack))

(define (push x)
  (set! stack (cons x stack))
  (display-stack))

(define (pop x y)
  (if (not (equal? (car stack) x))
      (error (format "Different! ~a ~a" (car stack) x))
      (void))
  (set! stack (cons (format "= ~a" y) (cdr stack)))
  (display-stack)
  (set! stack (cdr stack)))

(define-syntax (m stx)
  (syntax-case stx ()
    [(m x)
     (letrec [
      [w (lambda (x y)
           `(begin
              (push (quote ,x))
              (let [[r ,y]]
                (pop (quote ,x) r)
                r)))]
      [f (lambda (x)
           (if (pair? x)
               (w x
                  (cond [(eq? (car x) 'if)
                         (cons 'if (map f (cdr x)))]
                        [(eq? (car x) 'lambda)
                         (cons 'lambda (cons (cadr x) (map f (cddr x))))]
                        [(eq? (car x) 'letrec)
                         (cons 'letrec (cons (cons (cons (caaadr x)
                                              (cons (f (cadr (caadr x))) '())) '())
                                             (map f (cddr x))))]
                        [else
                         (map f x)]))
                  x))]]
       (datum->syntax stx (f (syntax->datum #'x))))]))

;(m (+ (+ 1 2) (+ 3 4)))
;(m (if true 1 2))

(m ((lambda (x) (if (eq? 0 x) "zero" "not zero")) (+ 1 2)))
(display "\n\n\n")
(m (letrec [[map (lambda (f l)
                    (if (empty? l) l (cons (f (car l)) (map f (cdr l)))))]]
     (map (lambda (x) (+ x 1)) (list 2 3))))
