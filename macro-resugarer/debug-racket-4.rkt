#lang racket

(define $redex 'gremlin)
(define $index 'gremlin)

(define $stk (list))
(define $path (list))
(define ($init-stk! x)
  (set! $stk (list x)))
(define ($push! n)
  (set! $path (cons n $path))
  (set! $stk (cons (vector-ref (car $stk) n) $stk)))
(define ($pop!)
  (set! $stk (cdr $stk))
  (set! $path (cdr $path)))
(define ($alter! x)
  (set! $stk (cons x (cdr $stk)))
  (when (not (empty? (cdr $stk)))
    (vector-set! (cadr $stk) (car $path) x)))
;  (when (vector? (car $stk))
;    (vector-set! (car $stk) (car $path) x)))
#|  (set! $term x)
  (when (not (empty? $stk))
    (vector-set! (car $stk) (car $path) x)))|#


#;(define $path (list))
#;(define ($push! n) (set! $path (cons n $path)))
#;(define ($pop!) (set! $path (cdr $path)))

#;(define ($alter! x [term $term] [path (reverse $path)])
  (cond [(empty? path)
         ($set-term! x)]
        [(eq? (length path) 1)
         (vector-set! term (car path) x)]
        [else
         ($alter! x [vector-ref term (car path)] (cdr path))]))

(define ($emit)
  (display (format "~a\n" (show (last $stk)))))

(define-syntax-rule (test-eval x)
  (Top x))

(define-struct Func (func term)
  #:property prop:procedure
  (λ (self . args) (apply (Func-func self) args)))

; Prepare a term to be shown
(define-syntax Adorn
  (syntax-rules (λ if set! begin +)
    [(Adorn (+ x y))
     `#(+ ,(Adorn x) ,(Adorn y))]
    [(Adorn (λ (v) x))
     (let [[v 'v]] `#(λ (v) ,(Adorn x)))]
    [(Adorn (f x))
     `#(,(Adorn f) ,(Adorn x))]
    [(Adorn x)
     x]))

(define-syntax-rule (Rec x n)
  (begin ($push! n)
         (let [[result (Eval x)]]
           ($pop!)
           result)))

; Augment code to show steps
(define-syntax-rule (Top x)
  (begin ($init-stk! (Adorn x))
         (let [[result (Eval x)]]
           ($emit)
           result)))

(define-syntax Eval
  (syntax-rules (λ if set! begin +)
    
    [(Eval (+ x y))
     (let [[xv (Rec x 1)]
           [yv (Rec y 2)]]
       (let [[result (+ xv yv)]]
         ($emit)
         ($alter! result)
         result))]
    
    [(Eval (λ (v) x))
     (Func (λ (v) (Eval x)) (Adorn (λ (v) x)))]
    
    [(Eval (f x))
     (let [[fv (Rec f 0)]
           [xv (Rec x 1)]]
       ($emit)
       ($alter! (vector-ref (Func-term fv) 2))
       (let [[result (fv xv)]]
         ($alter! result)
         result))]
    
    [(Eval x)
     x]))

(define (show x)
  (cond [(Func? x) (show (Func-term x))]
        [(vector? x) (vector->list (vector-map show x))]
        [(procedure? x) (object-name x)]
        [else x]))

(test-eval (+ 1 2))
(test-eval (+ (+ 1 2) (+ 3 4)))
(test-eval (+ (+ (+ 1 2) (+ 3 4)) (+ 5 (+ 6 7))))
(test-eval (λ (x) x))
(test-eval ((λ (x) x) 3))
(test-eval ((λ (x) (+ (+ 1 2) (+ 3 x))) (+ 2 3)))
(test-eval (+ 3 ((λ (x) (+ x 1)) 4)))