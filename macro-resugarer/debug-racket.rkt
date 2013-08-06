(module debug-racket racket

#| A simple debug stepper for racket.

  eval [L | x | R] = emit [L x R];
                     rec [L | x | R]

  rec [L | + x y | R]    =  x' := eval [L + | x | y R];
                            y' := eval [L + x' | y | R];
                            + x' y'

  rec [L | if x y z | R] =  x' := eval [L if | x | y z R];
                            if x'
                              then eval [L | y | R]
                              else eval [L | z | R]

  rec [L | f x | R]      =  f' := eval [L | f | x R];
                            x' := eval [L f' | x | R];
                            if Lamb? f'
                              then f' L R x'
                              else f' x'

  rec [L | \v -> x | R]  =  Lamb (\L R y ->
                                  eval [L | (\v -> Var 'v x) y | R])

  rec [L | Var v x | R]  =  x
|#

  (define-struct Lamb (fun patt) #:transparent)
  
  (define-struct Var (name value) #:transparent)
  
  (define-syntax-rule (test-eval patt)
    (Eval empty-ctx patt))
  
  (define-syntax-rule (Eval ctx patt)
    (let [[result (Rec ctx patt)]]
      (emit ctx (unwrap-patt result))
      (unwrap-value result)))
  
  (define last #f)
  
  (define (emit ctx patt)
    (let [[str (format "~a\n" (ctx patt))]]
      (when (not (equal? str last))
        (display str)
        (set! last str))
      patt))
  
  (define (unwrap-value x)
    (if (Var? x) (Var-value x) x))
  
  (define (unwrap-patt x)
    (cond [(Lamb? x) (Lamb-patt x)]
          [(Var? x) `(,(Var-name x) := ,(unwrap-patt (Var-value x)))]
          [else x]))
  
  (define empty-ctx (lambda (x) x))

  (define-syntax Rec
    (syntax-rules (λ lambda + if)
      [(Rec ctx (+ x y))
       (let* [[x* (Eval (λ (w) (ctx `(+ ,x y))) x)]
              [y* (Eval (λ (w) (ctx `(+ ,(unwrap-patt x*) ,y))) y)]]
         (+ x* y*))]
      [(Rec ctx (if x y z))
       (let [[x* (Eval (λ (w) (ctx `(if ,w y z))) x)]]
         (if x
             (Eval ctx y)
             (Eval ctx z)))]
      [(Rec ctx (λ vs x))
       (Rec ctx (lambda vs x))]
      [(Rec ctx (lambda (v) x))
       (Lamb (λ (ctx*)
               (λ (v)
                 (Var 'v (Eval ctx* x))))
             '(λ (v) x))]
      [(Rec ctx (f x))
       (let* [[f* (Eval (λ (w) (ctx `(,w x))) f)]
              [x* (Eval (λ (w) (ctx `(,(unwrap-patt f*) ,w))) x)]]
         (if (Lamb? f*)
             (((Lamb-fun f*) ctx) x*)
             (f* x*)))]
      [(Rec ctx x) x]))
  
  (test-eval (+ 1 (+ 2 3)))
  (test-eval ((λ (x) (+ x 1)) (+ 1 2)))
  (test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 1 2)))
  (test-eval (Var 'v 3))
  (test-eval (λ (x) x))
)
