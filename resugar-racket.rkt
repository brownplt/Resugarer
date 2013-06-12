(module resugar-racket racket
  (require "resugar.rkt")

  ; See debug-racket.rkt
  ; for a much cleaner presentation of the debugging approach.

  (define-struct Lamb (fun term) #:transparent)
  (define-struct Var (name value) #:transparent)
  
  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)
                          (string? t)
                          (procedure? t)
                          (pair? t)))
  
  (define (term->racket term)
    (λ (c) (pt/eval empty-ctx term c)))
  
  (define (pt/eval ctx term c_)
    (let [[expr (pt/rec ctx term c_)]]
      (with-syntax [[ctx* ctx]
                    [expr* expr]
                    [c* c_]]
        #'(let [[result expr*]]
            (emit ctx* (unwrap-term result) c*)
            (unwrap-value result)))))
  
  (define (tlist os . ts)
    (term-list os ts))
  
  (define (pt/rec ctx term c_)
    (match term
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (with-syntax [[ctx* ctx] [os* os_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) 'begin w))) x_ c_)]]
           #'x-eval*))]
      ; (+ x y)
      [(term-list os_ (list '+ x_ y_))
       (with-syntax [[(x-var* y-var*) (generate-temporaries #'(x y))]
                     [ctx* ctx] [y* y_] [os* os_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) '+ w y*))) x_ c_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) '+ (unwrap-term x-var*) w))) y_ c_)]]
           #'(let* [[x-var* x-eval*]
                    [y-var* y-eval*]]
               (+ x-var* y-var*))))]
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[(x-var*) (generate-temporaries #'(x))]
                     [ctx* ctx] [y* y_] [z* z_] [os* os_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) 'if w y* z*))) x_ c_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* w)) y_ c_)]
                       [z-eval* (pt/eval #'(λ (w) (ctx* w)) z_ c_)]]
           #'(let* [[x-var* x-eval*]]
               (if x-var* y-eval* z-eval*))))]
      ; (lambda (v) x) -> (λ (v) x)
      [(term-list os_ (cons 'lambda rest))
       (pt/rec ctx (term-list os_ (cons 'λ rest)) c_)]
      ; (λ (v) x)
      [(term-list os_ (list 'λ (term-list os2 (list (? symbol? v_))) x_))
       (with-syntax [[(ctx-var*) (generate-temporaries #'(ctx))]
                     [term* term]]
         (with-syntax [[x-eval* (pt/eval #'ctx-var* x_ c_)]
                       [v* v_]]
           #'(Lamb (λ (ctx-var*) (λ (v*) (Var 'v* x-eval*))) term*)))]
      ; (f x)
      [(term-list os_ (list f_ x_))
       (with-syntax [[(f-var* x-var*) (generate-temporaries #'(f_ x_))]
                     [ctx* ctx] [x* x_] [os* os_]]
         (with-syntax [[f-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) w x*))) f_ c_)]
                       [x-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) (unwrap-term f-var*) w))) x_ c_)]]
           #'(let* [[f-var* f-eval*]
                    [x-var* x-eval*]]
               (if (Lamb? f-var*)
                   (((Lamb-fun f-var*) ctx*) x-var*)
                   (f-var* x-var*)))))]
      ; (f x y)
      [(term-list os_ (list f_ x_ y_))
       (with-syntax [[(f-var* x-var* y-var*) (generate-temporaries #'(f_ x_ y_))]
                     [ctx* ctx] [x* x_] [y* y_] [os* os_]]
         (with-syntax [[f-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*)  w x* y*))) f_ c_)]
                       [x-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) (unwrap-term f-var*) w y*))) x_ c_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) (unwrap-term f-var*) (unwrap-term x-var*) w))) y_ c_)]]
           #'(let* [[f-var* f-eval*]
                    [x-var* x-eval*]
                    [y-var* y-eval*]]
               (if (Lamb? f-var*)
                   (((Lamb-fun f-var*) ctx*) x-var* y-var*)
                   (f-var* x-var* y-var*)))))]
      ; x
      [(? atomic? x_)
       (with-syntax [[x* x_]] #'x*)]))
  
  (define (emit ctx term c)
    (c (ctx term)))
  
  (define empty-ctx (λ (x) x))
  
  (define (unwrap-value x)
    (cond [(Var? x) (Var-value x)]
          [else x]))
  
  (define (unwrap-term x)
    (define (unwrap-var v)
      (let* [[name (Var-name v)]
             [term (unwrap-term (Var-value v))]
             [u (unexpand-term term)]]
        (if u u name)))
    (cond [(Lamb? x) (Lamb-term x)]
          [(Var? x) (unwrap-var x)]
          [(atomic? x) x]))
  
  (define-syntax-rule (test-term t)
    ((term->racket (make-term t)) (λ (x) (display (format "~a\n" x)))))
  
  (define (steps term emit)
    (eval (term emit)))
  
  (define-syntax-rule (test-eval t)
    (macro-aware-eval* term->racket steps (make-term t)))

  (define-macro Cond
    [(Cond [^ $else x])    x]
    [(Cond [^ x y])       (if x y (+ 0 0))]
    [(Cond [^ x y] z ...) (if x y (Cond z ...))])
  
  (define-macro Let
    [(Let [^ [^ [^ f x] e]] b)
     ((lambda (f) b) (lambda (x) e))]
    [(Let [^ [^ [^ f x] e] [^ xs es] ...] b)
     ((lambda (f) (Let [^ [^ xs es] ...] b)) (lambda (x) e))]
    [(Let [^ [^ x e]] b)
     ((lambda (x) b) e)]
    [(Let [^ [^ x e] [^ xs es] ...] b)
     ((lambda (x) (Let [^ [^ xs es] ...] b)) e)])
  
  (define-macro Or
    [(Or x) (begin x)]
    [(Or x y ys ...)
     ((λ (t) (if t t (Or y ys ...))) x)])
  
  (define-macro Inc
    [(Inc x) (+ x 1)])
  
  (set-debug-steps! #f)
  (set-debug-tags! #f)
  
  (test-eval 3)
  (test-term (+ 1 2))
  (test-eval (+ 1 2))
  (test-eval (+ (+ 1 2) (+ 3 4)))
  (test-eval (if #t (+ 1 2) (+ 3 4)))
  (test-eval (λ (x) x))
  (test-eval ((λ (x) (+ x 1)) 3))
  (test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
  (test-eval (+ 0 (car (cons (+ 1 2) (+ 3 4)))))
  (test-eval (Let [^ [^ x 1] [^ y (+ 1 2)]] (+ x y)))
  (test-eval (Or #f (+ 1 2)))
  (test-eval (Inc (+ 1 2)))
  (test-eval (Inc (+ (Inc 1) (Inc 2))))
  (test-eval (+ 1 (Cond [^ #f (+ 1 2)] [^ (Or #f #t) (+ 2 3)])))
)
