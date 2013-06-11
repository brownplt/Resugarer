(module resugar-racket racket
  (require "resugar.rkt")
  (require "pattern.rkt")

  ; See debug-racket.rkt
  ; for a much cleaner presentation of the debugging approach.

  (define-struct Lamb (fun patt) #:transparent)
  (define-struct Var (name value) #:transparent)
  
  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)
                          (string? t)
                          (procedure? t)
                          (pair? t)))
  
  (define (pattern->term patt)
    (λ (c) (pt/eval empty-ctx patt c)))
  
  (define (papp . xs)
    (plist (t-apply) xs))
  
  (define (binop? x)
    (and (symbol? x) (or (symbol=? x '+) (symbol=? x 'cons))))
  
  (define (pt/rec ctx patt c_)
    (match patt
      ; (+ x y)
      [(plist (t-apply) (list (constant '+) x_ y_))
       (with-syntax [[(x-var* y-var*) (generate-temporaries #'(x y))]
                     [ctx* ctx] [y* y_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (papp (constant '+) w y*))) x_ c_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* (papp (constant '+) (unwrap-patt x-var*) w))) y_ c_)]]
           #'(let* [[x-var* x-eval*]
                    [y-var* y-eval*]]
               (+ x-var* y-var*))))]
      ; (if x y z)
      [(plist (t-apply) (list (constant 'if) x_ y_ z_))
       (with-syntax [[(x-var*) (generate-temporaries #'(x))]
                     [ctx* ctx] [y* y_] [z* z_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (papp (constant 'if) w y* z*))) x_ c_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* w)) y_ c_)]
                       [z-eval* (pt/eval #'(λ (w) (ctx* w)) z_ c_)]]
           #'(let* [[x-var* x-eval*]]
               (if x-var* y-eval* z-eval*))))]
      ; (lambda (v) x) -> (λ (v) x)
      [(plist (t-apply) (cons (constant 'lambda) rest))
       (pt/rec ctx (plist (t-apply) (cons (constant 'λ) rest)) c_)]
      ; (λ (v) x)
      [(plist (t-apply) (list (constant 'λ) (plist (t-apply) (list (constant v_))) x_))
       (with-syntax [[(ctx-var*) (generate-temporaries #'(ctx))]
                     [patt* patt]]
         (with-syntax [[x-eval* (pt/eval #'ctx-var* x_ c_)]
                       [v* v_]]
           #'(Lamb (λ (ctx-var*) (λ (v*) (Var 'v* x-eval*))) patt*)))]
      ; (f x)
      [(plist (t-apply) (list f_ x_))
       (with-syntax [[(f-var* x-var*) (generate-temporaries #'(f_ x_))]
                     [ctx* ctx] [x* x_]]
         (with-syntax [[f-eval* (pt/eval #'(λ (w) (ctx* (papp  w x*))) f_ c_)]
                       [x-eval* (pt/eval #'(λ (w) (ctx* (papp (unwrap-patt f-var*) w))) x_ c_)]]
           #'(let* [[f-var* f-eval*]
                    [x-var* x-eval*]]
               (if (Lamb? f-var*)
                   (((Lamb-fun f-var*) ctx*) x-var*)
                   (f-var* x-var*)))))]
      ; (f x y)
      [(plist (t-apply) (list f_ x_ y_))
       (with-syntax [[(f-var* x-var* y-var*) (generate-temporaries #'(f_ x_ y_))]
                     [ctx* ctx] [x* x_] [y* y_]]
         (with-syntax [[f-eval* (pt/eval #'(λ (w) (ctx* (papp  w x* y*))) f_ c_)]
                       [x-eval* (pt/eval #'(λ (w) (ctx* (papp (unwrap-patt f-var*) w y*))) x_ c_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* (papp (unwrap-patt f-var*) (unwrap-patt x-var*) w))) y_ c_)]]
           #'(let* [[f-var* f-eval*]
                    [x-var* x-eval*]
                    [y-var* y-eval*]]
               (if (Lamb? f-var*)
                   (((Lamb-fun f-var*) ctx*) x-var* y-var*)
                   (f-var* x-var* y-var*)))))]
      ; (tag p o)
      [(tag x_ o_)
       (with-syntax [[o* o_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (tag w o*)) x_ c_)]]
           #'x-eval*))]
      ; x
      [(constant x_)
       (with-syntax [[x* x_]] #'x*)]))
  
  (define (pt/eval ctx patt c_)
    (let [[term (pt/rec ctx patt c_)]]
      (with-syntax [[ctx ctx]
                    [expr term]
                    [c_ c_]]
        #'(let [[result expr]]
            (emit ctx (unwrap-patt result) c_)
            (unwrap-value result)))))
  
  (define (emit ctx patt c)
    (c (ctx patt)))
  
  (define last #f)
  (define (emit_ patt)
    (let [[str (show-pattern patt)]]
      (when (not (equal? str last))
        (display str)
        (newline)
        (set! last str))))
  
  (define empty-ctx (λ (x) x))
  
  (define (unwrap-value x)
    (cond [(Var? x) (Var-value x)]
          [else x]))
  
  (define (unwrap-patt x)
    (cond [(Lamb? x) (Lamb-patt x)]
          [(Var? x) (papp (constant (Var-name x)) (constant ':=) (unwrap-patt (Var-value x)))]
          [(atomic? x) (constant x)]
          [else x]))
  
  (define-syntax-rule (test-term patt)
    (pattern->term (make-pattern patt)))
  
  (define-syntax-rule (test-eval-direct patt)
    (unwrap-value (eval ((test-term patt) emit_))))
  
  (define (steps term emit)
    (eval (term emit)))
  
  (define-syntax-rule (test-eval patt)
    (macro-aware-eval* pattern->term steps (make-pattern patt)))

  (define-macro Cond
    [(Cond [^ $else x])    x]
    [(Cond [^ x y])       (if x y (+ 0 0))]
    [(Cond [^ x y] z ...) (if x y (Cond z ...))])
  
  (define-macro L
    [(L [^ [^ x e]] b)
     ((λ (x) b) e)])
  
  (define-macro Let
    [(Let [^ [^ [^ f x] e]] b)
     ((lambda (f) b) (lambda (x) e))]
    [(Let [^ [^ [^ f x] e] [^ xs es] ...] b)
     ((lambda (f) (Let [^ [^ xs es] ...] b)) (lambda (x) e))]
    [(Let [^ [^ x e]] b)
     ((lambda (x) b) e)]
    [(Let [^ [^ x e] [^ xs es] ...] b)
     ((lambda (x) (Let [^ [^ xs es] ...] b)) e)])
  
  (set-debug-steps! #t)
  
  (test-eval 3)
  (test-eval (+ 1 2))
  (test-eval (+ (+ 1 2) (+ 3 4)))
  (test-eval (if #t (+ 1 2) (+ 3 4)))
  (test-eval (λ (x) x))
  (test-eval ((λ (x) (+ x 1)) 3))
  (test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
  (macro-aware-eval* pattern->term steps (tag (constant 3) (o-branch)))
  (test-eval (+ 1 (Cond [^ #f (+ 1 2)] [^ #f (+ 2 3)])))
  (test-eval (+ 0 (car (cons (+ 1 2) (+ 3 4)))))
  ; Problem: In (lambda (x) y), (x) is getting tagged!
  ;(test-expand (L [^ [^ x 1]] x))
  ;(test-eval (Let [^ [^ x 1] [^ y (+ 1 2)]] (+ x y)))
)
