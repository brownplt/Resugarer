#lang racket

(define-syntax-rule (test-eval x)
  (Eval x))

(define-syntax (test-code stx)
  (syntax-case stx ()
    [(test-code x)
     (let [[z (local-expand #'(Eval x) 'expression (list))]]
       (with-syntax [[z* z]]
         #''z*))]))

(define-struct Func (func term)
  #:property prop:procedure
  (λ (self . args) (apply (Func-func self) args)))

; Prepare a term to be shown
(define-syntax Adorn
  (syntax-rules (λ if set! begin)
    [(Adorn (begin x y))
     `(begin ,(Adorn x) ,(Adorn y))]
    [(Adorn (λ (v) x))
     (let [[v 'v]] `(λ (v) ,(Adorn x)))]
    [(Adorn (set! v x))
     (let [[v 'v]] `(set! v ,(Adorn x)))]
    [(Adorn (if x y z))
     `(if ,(Adorn x) ,(Adorn y) ,(Adorn z))]
    [(Adorn (f x))
     `(,(Adorn f) ,(Adorn x))]
    [(Adorn (f x y))
     `(,(Adorn f) ,(Adorn x) ,(Adorn y))]
    [(Adorn x)
     x]))

; Augment code to show steps
(define-syntax Eval
  (syntax-rules (λ if set! begin)
    
    [(Eval (begin x y))
     (let [[$x (Call (Eval x) (λ (_) `(begin ,_ ,(Adorn y))))]]
       (emit `(begin ,$x ,(Adorn y)))
       (Eval y))]
    
    [(Eval (if x y z))
     (let [[$x (Call (Eval x) (λ (_) `(if ,_ ,(Adorn y) ,(Adorn z))))]]
       (emit `(if ,$x ,(Adorn y) ,(Adorn z)))
       (if $x (Eval y) (Eval z)))]
    
    [(Eval (λ (v) x))
     (Func (λ (v) (Eval x)) (Adorn (λ (v) x)))]
    
    [(Eval (set! v x))
     (let [[$x (Call (Eval x) (λ (_) `(set! v ,_)))]]
       (emit `(set! v ,$x))
       (set! v $x))]
    
    [(Eval (f x))
     (let [[$f (Call (Eval f) (λ (_) `(,_ ,(Adorn x))))]]
       (let [[$x (Call (Eval x) (λ (_) `(,$f ,_)))]]
         (emit `(,$f ,$x))
         (if (Func? $f)
             ($f $x)
             (Call ($f $x) (λ (_) `(?? ,_))))))]
    
    [(Eval (f x y))
     (let [[$f (Call (Eval f) (λ (_) `(,_ ,(Adorn x) ,(Adorn y))))]]
       (let [[$x (Call (Eval x) (λ (_) `(,$f ,_ ,(Adorn y))))]]
         (let [[$y (Call (Eval y) (λ (_) `(,$f ,$x ,_)))]]
           (emit `(,$f ,$x ,$y))
           (if (Func? $f)
               ($f $x $y)
               (Call ($f $x $y) (λ (_) `(?? ,_)))))))]

    [(Eval x) x]))


(define (show x)
  (cond [(Func? x) (show (Func-term x))]
        [(list? x) (map show x)]
        [(procedure? x) (object-name x)]
        [else x]))

;;; Contexts ;;;

(define $val 'gremlin)
(define $ctx (list))

(define-syntax-rule (Call x c)
  (begin (push c)
         (set! $val x)
         (pop)
         $val))

(define (emit x [ctx $ctx])
  (if (empty? ctx)
      (begin (display (show x)) (newline))
      (emit ((car ctx) x) (cdr ctx))))

(define (push x)
  (set! $ctx (cons x $ctx)))

(define (pop)
  (set! $ctx (cdr $ctx)))


(define (external f) (* 2 (f (f 223))))

(test-eval (+ 1 2))
(test-eval (+ (+ 1 2) 3))
(test-eval (+ 1 (+ 2 3)))
(test-eval (+ (+ 1 2) (+ 3 4)))
(test-eval (if (+ 1 2) (+ 3 4) (+ 5 6)))
(test-eval (λ (x) (+ x 1)))
(test-eval (+ 8 ((λ (x) (+ x 1)) (+ 1 2))))
(test-eval ((λ (x) (+ x 1)) (+ 2 3)))
(test-eval (begin (+ 1 2) (+ 3 4)))
(test-eval ((λ (x) (begin (set! x (+ x 1)) (+ x 2))) (+ 3 4)))
(test-eval (+ 1 (external (λ (x) (+ 1 x)))))