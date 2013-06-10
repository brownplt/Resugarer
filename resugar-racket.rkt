(module resugar-racket racket
  (require "resugar.rkt")
  (require "pattern.rkt")

  ; See debug-racket.rkt
  ; for a much cleaner presentation of the debugging approach.

  (define-struct Lamb (fun patt) #:transparent)
  (define-struct Var (name value) #:transparent)
  
  (define-syntax-rule (pattern->term patt)
    (pt/eval empty-ctx patt))
  
  (define (papp . xs)
    (plist (t-apply) xs))
  
  (define (term->pattern x)
    (match x
      [(? atomic? x)
       (constant x)]))
  
  (define (pt/rec ctx patt)
    (match patt
      ; (+ x y)
      [(plist (t-apply) (list (constant '+) x_ y_))
       (with-syntax [[(x-var* y-var*) (generate-temporaries #'(x y))]
                     [ctx* ctx] [y* y_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (papp (constant '+) w y*))) x_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* (papp (constant '+) (unwrap-patt x-var*) w))) y_)]]
           #'(let* [[x-var* x-eval*]
                    [y-var* y-eval*]]
               (+ x-var* y-var*))))]
      ; (if x y z)
      [(plist (t-apply) (list (constant 'if) x_ y_ z_))
       (with-syntax [[(x-var*) (generate-temporaries #'(x))]
                     [ctx* ctx] [y* y_] [z* z_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (papp (constant 'if) w y* z*))) x_)]
                       [y-eval* (pt/eval #'(λ (w) (ctx* w)) y_)]
                       [z-eval* (pt/eval #'(λ (w) (ctx* w)) z_)]]
           #'(let* [[x-var* x-eval*]]
               (if x-var* y-eval* z-eval*))))]
      ; (λ (v) x)
      [(plist (t-apply) (list (constant 'λ) (plist (t-apply) (list (constant v_))) x_))
       (with-syntax [[(ctx-var*) (generate-temporaries #'(ctx))]
                     [patt* patt]]
         (with-syntax [[x-eval* (pt/eval #'ctx-var* x_)]
                       [v* v_]]
           #'(Lamb (λ (ctx-var*) (λ (v*) (Var 'v* x-eval*))) patt*)))]
      ; (f x)
      [(plist (t-apply) (list f_ x_))
       (with-syntax [[(f-var* x-var*) (generate-temporaries #'(f_ x_))]
                     [ctx* ctx] [x* x_]]
         (with-syntax [[f-eval* (pt/eval #'(λ (w) (ctx* (papp  w x*))) f_)]
                       [x-eval* (pt/eval #'(λ (w) (ctx* (papp (unwrap-patt f-var*) w))) x_)]]
           #'(let* [[f-var* f-eval*]
                    [x-var* x-eval*]]
               (if (Lamb? f-var*)
                   (((Lamb-fun f-var*) ctx*) x-var*)
                   (f-var* x-var*)))))]
      ; x
      [(constant x_)
       (with-syntax [[x* x_]] #'x*)]))
  
  (define (pt/eval ctx patt)
    (let [[term (pt/rec ctx patt)]]
      (with-syntax [[ctx ctx]
                    [expr term]]
        #'(let [[result expr]]
            (emit ctx (unwrap-patt result))
            (unwrap-value result)))))
  
  (define last #f)
  (define (emit ctx patt)
    (let [[str (show-pattern (ctx patt) #t)]]
      (when (not (equal? str last))
        (display str) (newline)
        (set! last str))))
  
  (define empty-ctx (λ (x) x))
  
  (define (unwrap-value x)
    (if (Var? x) (Var-value x) x))
  
  (define (unwrap-patt x)
    (cond [(Lamb? x) (Lamb-patt x)]
          [(Var? x) (papp (constant (Var-name x)) (constant ':=) (unwrap-patt (Var-value x)))]
          [(atomic? x) (constant x)]
          [else x]))
  
  (define-syntax-rule (test-term patt)
    (pattern->term (make-pattern patt)))
  
  (define-syntax-rule (test-eval patt)
    (eval (test-term patt)))
  
  (test-eval 3)
  (test-eval (+ 1 2))
  (test-eval (+ (+ 1 2) (+ 3 4)))
  (test-eval (if #t (+ 1 2) (+ 3 4)))
  (test-eval (λ (x) x))
  (test-eval ((λ (x) (+ x 1)) 3))
  (test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
)
