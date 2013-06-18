(module resugar-racket racket
  (require "resugar.rkt")

  ; See debug-racket.rkt
  ; for a much cleaner presentation of the debugging approach.

  (define-struct Var (name value) #:transparent)
  (define-struct PleaseYieldFunc (ctx))
  (define-struct YieldedFunc (func))
  (define-struct PleaseYieldTerm ())
  (define-struct YieldedTerm (term))
  
  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)
                          (string? t)
                          (procedure? t)
                          (pair? t)
                          (null? t)
                          (void? t)))
  
  (define SHOW_PROC_NAMES #t)
  
  ; A global table of our annotated functions,
  ; to tell them apart from ordinary functions.
  (define annotated-funcs (set))
  (define (annotated-func f)
    (when (not (set-member? annotated-funcs f))
      (set! annotated-funcs (set-add annotated-funcs f)))
    f)
  
  (define (call-annotated-func f ctx . args)
    (if (set-member? annotated-funcs f)
        (apply (f (PleaseYieldFunc ctx)) args)
        (apply f args)))
  
  (define (value->term x)
    (cond [(and (procedure? x) (set-member? annotated-funcs x))
           (x (PleaseYieldTerm))]
          [(and SHOW_PROC_NAMES (procedure? x) (object-name x))
           (object-name x)]
          [else x]))
  
  (define (term->racket term)
    (λ (emit) (pt/eval term empty-ctx emit)))
  
  (define (pt/eval term_ ctx_ emit_)
    (with-syntax [[ctx* ctx_]
                  [term* (adorn term_)]
                  [rest* (pt/rec term_ ctx_ emit_)]
                  [emit* emit_]]
      #'(begin (emit* (ctx* term*))
               rest*)))
  
  (define empty-ctx (λ (x) x))
  (define (unknown-ctx ctx)
    (λ (x) (ctx (term-list (list) (list '?? x)))))
  
  
  ; Prepare a term for printing
  (define (adorn term_)
    (match term_
      
      [(term-id os_ x_)
       (with-syntax [[os* os_]
                     [x* (adorn x_)]]
         #'(term-id (list . os*) x*))]
      
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (with-syntax [[os* os_]
                     [x* (adorn x_)]]
       #'(term-list (list . os*) (list 'begin x*)))]
      
      ; (begin x y)
      [(term-list os_ (list 'begin x_ y_))
       (with-syntax [[os* os_]
                     [x* (adorn x_)]
                     [y* (adorn y_)]]
         #'(term-list (list . os*) (list 'begin x* y*)))]
      
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[os* os_]
                     [x* (adorn x_)]
                     [y* (adorn y_)]
                     [z* (adorn z_)]]
         #'(term-list (list . os*) (list 'if x* y* z*)))]
      
      ; (lambda (v) x)
      [(term-list os_ (cons 'lambda rest))
       (adorn (term-list os_ (cons 'λ rest)))]
      
      ; (λ (v) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? v_))) x_))
       (with-syntax [[os* os_]
                     [os2* os2_]
                     [v* v_]
                     [x* (adorn x_)]]
         #'(let [[v* 'v*]]
             (term-list (list . os*) (list 'λ (term-list (list . os2*) (list v*)) x*))))]
      
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[os* os_]
                     [v* v_]
                     [x* (adorn x_)]]
         #'(term-list (list . os*) (list 'set! 'v* x*)))]
      
      ; (f)
      [(term-list os_ (list f_))
       (with-syntax [[os* os_]
                     [f* (adorn f_)]]
         #'(term-list (list . os*) (list f*)))]
      
      ; (f x)
      [(term-list os_ (list f_ x_))
       (with-syntax [[os* os_]
                     [f* (adorn f_)]
                     [x* (adorn x_)]]
         #'(term-list (list . os*) (list f* x*)))]
      
      ; (f x y)
      [(term-list os_ (list f_ x_ y_))
       (with-syntax [[os* os_]
                     [f* (adorn f_)]
                     [x* (adorn x_)]
                     [y* (adorn y_)]]
         #'(term-list (list . os*) (list f* x* y*)))]
      
      ; value c
      [c_
       (with-syntax [[c* c_]]
         #'(value->term c*))]))
  
  
  ; The recursive part of pt/eval; instrument a term with emit statements to make a stepper
  (define (pt/rec term_ ctx_ emit_)
    (with-syntax [[ctx* ctx_]]
    (match term_
      
      [(term-id os_ x_)
       (with-syntax [[os* os_] [x* (adorn x_)]]
         (pt/rec x_ #'(λ (__) (ctx* (term-id (list . os*) x*))) emit_))]
      
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (pt/eval x_ ctx_ emit_)]
      
      ; (begin x y)
      [(term-list os_ (list 'begin x_ y_))
       (with-syntax [[os* os_]
                     [y* (adorn y_)]]
         (with-syntax [[x* (pt/rec x_ #'(λ (__) (ctx* (term-list (list . os*) (list 'begin (value->term __) y*)))) emit_)]
                       [y* (pt/eval (term-list os_ (list 'begin y_)) ctx_ emit_)]]
           #'(begin x* y*)))]
      
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[os* os_]
                     [y* (adorn y_)]
                     [z* (adorn z_)]]
         (with-syntax [[x* (pt/rec x_ #'(λ (__) (ctx* (term-list (list . os*) (list 'if __ y* z*)))) emit_)]
                       [ry* (pt/eval y_ ctx_ emit_)]
                       [rz* (pt/eval z_ ctx_ emit_)]]
           #'(if x* ry* rz*)))]
      
      ; (lambda (v) x)
      [(term-list os_ (cons 'lambda rest))
       (pt/rec (term-list os_ (cons 'λ rest)) ctx_ emit_)]
      
      ; (λ (v) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? v_))) x_))
       (with-syntax [[(fv* cv*) (generate-temporaries #'(f c))]
                     [os* os_]
                     [v* v_]]
         (with-syntax [[func-body* (pt/eval x_ #'(PleaseYieldFunc-ctx cv*) emit_)]
                       [mime-func-body* (pt/eval x_ #'(unknown-ctx ctx*) emit_)]
                       [term* (adorn term_)]]
           #'(annotated-func
              (λ (cv*)
                (cond [(PleaseYieldFunc? cv*)
                       (λ (v*) func-body*)]
                      [(PleaseYieldTerm? cv*)
                       term*]
                      [else
                       ((λ (v*) mime-func-body*) cv*)])))))]
      
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[os* os_]
                     [v* v_]]
         (with-syntax [[x* (pt/rec x_ #'(λ (__) (ctx* (term-list (list . os*) (list 'set! 'v* (value->term __))))) emit_)]]
           #'(set! v* x*)))]
      
      ; (f)
      [(term-list os_ (list f_))
       (with-syntax [[(fv* rv*) (generate-temporaries #'(f r))]
                     [os* os_]
                     [f* (adorn f_)]]
         (with-syntax [[f* (pt/rec f_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term __))))) emit_)]
                       [r* (pt/rec #'rv* ctx_ emit_)]]
           #'(let* [[fv* f*]
                    [rv* (call-annotated-func fv* ctx*)]]
               r*)))]
      
      ; (f x)
      [(term-list os_ (list f_ x_))
       (with-syntax [[(fv* xv* rv*) (generate-temporaries #'(f x r))]
                     [os* os_]
                     [f* (adorn f_)]
                     [x* (adorn x_)]]
         (with-syntax [[f* (pt/rec f_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term __) x*)))) emit_)]
                       [x* (pt/rec x_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term fv*) (value->term __))))) emit_)]
                       [r* (pt/rec #'rv* ctx_ emit_)]]
           #'(let* [[fv* f*]
                    [xv* x*]
                    [rv* (call-annotated-func fv* ctx* xv*)]]
               r*)))]
      
      ; (f x y)
      [(term-list os_ (list f_ x_ y_))
       (with-syntax [[(fv* xv* yv* rv*) (generate-temporaries #'(f x y r))]
                     [os* os_]
                     [f* (adorn f_)]
                     [x* (adorn x_)]
                     [y* (adorn y_)]]
         (with-syntax [[f* (pt/rec f_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term __) x* y*)))) emit_)]
                       [x* (pt/rec x_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term fv*) (value->term __) y*)))) emit_)]
                       [y* (pt/rec y_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term fv*) (value->term xv*) __)))) emit_)]
                       [r* (pt/eval #'rv* ctx_ emit_)]]
           #'(let* [[fv* f*]
                    [xv* x*]
                    [yv* y*]
                    [rv* (call-annotated-func fv* ctx* xv* yv*)]]
               r*)))]
      
      ; value x
      [x_
       (with-syntax [[x* x_]]
         #'x*)]
      )))

  (define (emit x)
    (λ (x) (display (format "~a\n" x))))
  
  (define-syntax-rule (test-term t)
    (syntax->datum ((term->racket (make-term t)) emit)))
  
  (define (steps term emit)
    (eval (term emit)))
  
  (define-syntax-rule (test-eval t)
    (macro-aware-eval* term->racket steps (make-term t)))

  (define-macro Cond
    [(Cond [^ $else x])   x]
    [(Cond [^ x y])       (if x y (+ 0 0))]
    [(Cond [^ x y] z ...) (if x y (! Cond z ...))])
  
  (define-macro Let
    [(Let [^ [^ [^ f x] e]] b)
     ((lambda (f) b) (lambda (x) e))]
    [(Let [^ [^ [^ f x] e] [^ xs es] ...] b)
     ((lambda (f) (Let [^ [^ xs es] ...] b)) (lambda (x) e))]
    [(Let [^ [^ x e]] b)
     ((lambda (x) b) e)]
    [(Let [^ [^ x e] [^ xs es] ...] b)
     ((lambda (x) (Let [^ [^ xs es] ...] b)) e)])
  
  (define-macro Set
    [(Set [^ [^ [^ f x] e]] b)
     (begin (set! f (lambda (x) e)) b)]
    [(Set [^ [^ [^ f x] e] xs ...] b)
     (begin (set! f (lambda (x) e)) (Set [^ xs ...] b))]
    [(Set [^ [^ x e]] b)
     (begin (set! x e) b)]
    [(Set [^ [^ x e] xs ...] b)
     (begin (set! x e) (Set [^ xs ...] b))])

  (define-macro Letrec
    [(Letrec [^ [^ x e] ...] b)
     (Let [^ [^ x 0] ...]
          (Set [^ [^ x e] ...]
               b))])
  
  (define-macro Or
    [(Or x) (begin x)]
    [(Or x y ys ...)
     ((λ (t) (if t t (Or y ys ...))) x)])
  
  (define-macro And
    [(And x) (begin x)]
    [(And x y ys ...)
     (if x (And y ys ...) #f)])
  
  (define-macro Just
    [(Just x) x])
  
  (define-macro Let1
    [(Let1 v x y)
     ((λ (v) y) x)])
  
  (define-macro Inc
    [(Inc x) (+ x 1)])
  
  (define-macro Inc2
    [(Inc2 x) (+ 1 (Inc x))])
  
  (define (string-first x)
    (substring x 0 1))
  
  (define (string-rest x)
    (substring x 1))
  
  (define-macro Cdavr
    [(Cdavr input)
     (Letrec [^ [^ [^ init x]
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "c" head) (! more tail)]
                                  [^ $else #f])))]
                [^ [^ more x]
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "a" head) (! more tail)]
                                  [^ (equal? "d" head) (! more tail)]
                                  [^ (equal? "r" head) (! end tail)]
                                  [^ $else #f])))]
                [^ [^ end x]
                   (equal? x "")]]
             (! init input))])
  
  (set-debug-steps! #f)
  (set-debug-tags! #f)
  
  (define (my-external-function f)
    (f (f 17)))
  
  (test-eval 3)
  (test-term (+ 1 2))
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
  (test-eval (Or #f #t))
  (test-eval (Or #f (+ 1 2)))
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
  (test-eval (Letrec [^ [^ [^ f n] (g n)] [^ [^ g n] (+ n 1)]] (f 3)))
  (test-eval (Or (zero? 3) (sub1 3)))
  (test-eval (And (not (zero? 3)) (sub1 3)))
  (test-eval (! + 1 2))
  ;(test-eval (Letrec [^ [^ [^ f n] (if (zero? n) 77 (f 0))]] (f 0))) ; loops!
  (show-term (test-expand (Letrec [^ [^ [^ f n] (if (zero? n) 77 (f 0))]] (f 0))))
  #|
  (test-eval (Letrec [^ [^ [^ is-even? n] (! Or (zero? n) (! is-odd? (sub1 n)))]
                        [^ [^ is-odd? n] (! And (not (zero? n)) (! is-even? (sub1 n)))]]
                     (is-odd? 11)))
  (test-eval (begin (+ 1 2) (+ 3 4)))
  (test-eval ((λ (f) (begin (set! f (λ (x) x)) (f 4))) 3))
  
  (test-eval (Cdavr "cadr"))
  (test-eval (Cdavr "cdad"))
  (time (test-eval (Letrec [^ [^ [^ fib n]
                                 (if (Or (eq? n 0) (eq? n 1)) 1 (+ (fib (- n 1)) (fib (- n 2))))]]
                           (fib 25))))
  (time (letrec ((fib (λ (n) (if (or (eq? n 0) (eq? n 1)) 1 (+ (fib (- n 1)) (fib (- n 2)))))))
          (fib 25)))
  ;(test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
  ;(test-eval ((lambda (s) (Let [^ [^ x (string-first s)] [^ y (string-rest s)]] y)) "abc"))
  ;(test-eval ((λ (x) (x x)) (λ (x) x)))
|#
)
