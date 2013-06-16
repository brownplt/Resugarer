(module debug-racket-2 racket

  (define-struct Var (name value) #:transparent)
  
  (define (emit patt ctx)
    (display (format "~a\n" (ctx patt))))

  (define empty-ctx (λ (x) x))
  (define (unknown-ctx ctx)
    (λ (x) (ctx `(?? ,x))))
  
  (define-syntax-rule (test-eval patt)
    (Eval patt empty-ctx))
  
  (define-syntax Adorn
    (syntax-rules (λ + * if)
      [(Adorn (λ (v ...) x))
       (let [[v 'v] ...] `(λ (,v ...) ,(Adorn x)))]
      [(Adorn (+ x y))
       `(+ ,(Adorn x) ,(Adorn y))]
      [(Adorn (* x y))
       `(* ,(Adorn x) ,(Adorn y))]
      [(Adorn (if x y z))
       `(if ,(Adorn x) ,(Adorn y) ,(Adorn z))]
      [(Adorn (f x))
       `(,(Adorn f) ,(Adorn x))]
      [(Adorn c) (show c)]))
  
  (define-syntax-rule (Eval patt ctx)
    (begin (emit (Adorn patt) ctx)
           (Rec patt ctx)))
  
  ; Instrumented functions
  
  (define-struct PleaseYieldFunc (ctx))
  (define-struct YieldedFunc (func))
  (define-struct PleaseYieldPatt ())
  (define-struct YieldedPatt (patt))
  
  (define (show x)
    ;x
    (if (procedure? x)
        (let [[p (with-handlers [[(λ (__unused) #t)
                                  (λ (__unused) x)]]
                   (x (PleaseYieldPatt)))]]
          (if (YieldedPatt? p)
              (YieldedPatt-patt p)
              x))
        x))
  
  (define-syntax Rec
    (syntax-rules (λ + * if)
      
      [(Rec (+ x y) ctx)
       (let* [[x* (Rec x (λ (_) (ctx `(+ ,_ ,(Adorn y)))))]
              [y* (Rec y (λ (_) (ctx `(+ ,x* ,_))))]
              [z* (+ x* y*)]]
         (Eval z* ctx))]
      
      [(Rec (if x y z) ctx)
       (let* [[x* (Rec x (λ (_) (ctx `(if ,_ ,(Adorn y) ,(Adorn z)))))]]
         (if x* (Eval y ctx) (Eval z ctx)))]
      
      [(Rec (λ vs x) ctx)
       ; We need to return something which *acts* like a procedure,
       ; so that it can be called by external code, but can also,
       ; * print itself nicely
       ;   (takes a (PleaseYieldPatt), wraps its output in a YieldedPatt)
       ; * take a ctx as an arg for future printing
       ;   (takes a (PleaseYieldFunc ctx), signs its output with a YieldedFunc)
       (λ (c*)
         (cond [(PleaseYieldFunc? c*)
                (YieldedFunc (λ vs (Eval x (PleaseYieldFunc-ctx c*))))]
               [(PleaseYieldPatt? c*)
                (YieldedPatt (Adorn (λ vs x)))]
               [else ((λ vs (Eval x (unknown-ctx ctx))) c*)]))]
      
      [(Rec (f x) ctx)
       (let* [[f* (Rec f (λ (_) (ctx `(,(Adorn _) ,(Adorn x)))))]
              [x* (Rec x (λ (_) (ctx `(,(Adorn f*) ,(Adorn _)))))]]
         (let [[func (with-handlers [[(λ (__unused) #t)
                                      (λ (__unused) f*)]]
                       (f* (PleaseYieldFunc ctx)))]]
           (if (YieldedFunc? func)
               ((YieldedFunc-func func) x*) ; 'f' evaluated to an instrumented function
               (f* x*))))] ; 'f' evaluated to an ordinary function
      [(Rec x ctx)
       x]))
  
  (define (my-external-function f)
    (f (f 17)))
  
  (test-eval 3)
  (test-eval (+ 1 2))
  (test-eval (+ (+ 1 2) 3))
  (test-eval (+ 1 (+ 2 3)))
  (test-eval (+ (+ 1 2) (+ 3 4)))
  (test-eval (if #t 1 2))
  (test-eval (if (+ 1 2) (+ 3 4) (+ 5 6)))
  (test-eval (cons 1 (cons 1 2)))
  (test-eval (λ (x) x))
  (test-eval ((λ (x) (+ x 1)) 3))
  (test-eval ((λ (x) (+ x x)) 3))
  (test-eval ((λ (x) (+ x 1)) (+ 1 2)))
  (test-eval ((λ (x) x) (λ (x) x)))
  (test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 1 2)))
  (test-eval (+ 1 (my-external-function (λ (x) (+ x 1)))))
  
)