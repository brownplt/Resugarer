(module resugar-racket racket
  (provide (all-defined-out))
  (require "resugar.rkt")
  (require profile)

  ; See debug-racket.rkt
  ; for a much cleaner presentation of the debugging approach.
  
  ; TODO: hook up macro validation
  ; TODO: add 'let' language primitive to stepper

  (define-struct Var (name value) #:transparent)
  (define-struct Func (term annot bare)
    #:property prop:procedure
    (λ (self . args) (apply (Func-bare self) args)))
  
  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)
                          (string? t)
                          (procedure? t)
                          (pair? t)
                          (null? t)
                          (void? t)))
  
  (define SHOW_PROC_NAMES #t)
  (define DEBUG_VARS #f)
  (define (set-debug-vars! x)
    (set! DEBUG_VARS x))
  
  (define-syntax-rule (call-func f ctx args ...)
    (if (Func? f)
        (((Func-annot f) ctx) args ...)
        (f args ...)))

  (define (value->term x)
    (cond [DISABLED
           #f]
          [(Func? x)
           (Func-term x)]
          [(Var? x)
           (let* [[name (Var-name x)]
                  [val (Var-value x)]
                  [u (unexpand-term (value->term val))]]
             (if DEBUG_VARS
                 (term-list (list) (list name ':= (strip-term-tags (value->term val))))
                 (if (could-not-unexpand? u)
                     (begin (debug "\nCould not unexpand: ~a := ~a\n"
                                   name (show-term (value->term val) #t)) name)
                     u)))]
          [(and SHOW_PROC_NAMES (procedure? x) (object-name x))
           (object-name x)]
          [else x]))
  
  (define (term->racket term)
    (λ (emit) (pt/top term empty-ctx emit)))
  
  (define ctx-var (car (generate-temporaries #'(ctx))))
  (define emit-var (car (generate-temporaries #'(emit))))
  
  (define (pt/top term_ ctx_ emit_)
    (with-syntax [[ctxv* ctx-var]
                  [emitv* emit-var]
                  [ctx* ctx_]
                  [emit* emit_]
                  [term* (pt/eval term_)]]
      #'(let [[ctxv* ctx*] [emitv* emit*]] term*)))
  
  (define (pt/eval term_)
    (with-syntax [[ctxv* ctx-var]
                  [emitv* emit-var]
                  [term* (adorn term_)]
                  [rest* (pt/rec term_)]]
      (if DISABLED
          #'rest*
          #'(begin (emitv* (ctxv* term*))
                   rest*))))
  
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
      
      ; (begin x y ys ...)
      [(term-list os_ (list 'begin x_ y_ ys_ ...))
       (with-syntax [[os* os_]
                     [x* (adorn x_)]
                     [y* (adorn y_)]
                     [(ys* ...) (map adorn ys_)]]
         #'(term-list (list . os*) (list 'begin x* y* ys* ...)))]
      
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[os* os_]
                     [x* (adorn x_)]
                     [y* (adorn y_)]
                     [z* (adorn z_)]]
         #'(term-list (list . os*) (list 'if x* y* z*)))]
      
      ; (lambda (v ...) x)
      [(term-list os_ (cons 'lambda rest))
       (adorn (term-list os_ (cons 'λ rest)))]
      
      ; (λ (v ...) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? vs_) ...)) x_))
       (with-syntax [[os* os_]
                     [os2* os2_]
                     [(vs* ...) vs_]
                     [x* (adorn x_)]]
         #'(let [[vs* 'vs*] ...]
             (term-list (list . os*) (list 'λ (term-list (list . os2*) (list vs* ...)) x*))))]
      
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[os* os_]
                     [v* v_]
                     [x* (adorn x_)]]
         #'(term-list (list . os*) (list 'set! 'v* x*)))]
      
      [(term-list os_ (list f_ xs_ ...))
       (with-syntax [[os* os_]
                     [f* (adorn f_)]
                     [(xs* ...) (map adorn xs_)]]
         #'(term-list (list . os*) (list f* xs* ...)))]
      
      ; value c
      [c_
       (with-syntax [[c* c_]]
         (if (symbol? c_)
             #'(value->term (Var 'c* c*))
             #'(value->term c*)))]))
  
  
  (define (pt/rec/ctx term_ ctx_)
    (with-syntax [[ctxv* ctx-var]
                  [ctx* ctx_]
                  [x* (pt/rec term_)]]
      (if DISABLED
          #'x*
          #'(let [[ctxv* ctx*]] x*))))
  
  
  ; The recursive part of pt/eval; instrument a term with emit statements to make a stepper
  (define (pt/rec term_)
    (with-syntax [[ctx* ctx-var]]
    (match term_
      
      [(term-id os_ x_)
       (with-syntax [[os* os_]
                     [x* (adorn x_)]]
         (pt/rec/ctx x_ #'(λ (__) (ctx* (term-id (list . os*) x*)))))]
      
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (pt/eval x_)]
      
      ; (begin x y ys ...)
      [(term-list os_ (list 'begin x_ y_ ys_ ...))
       (with-syntax [[os* os_]
                     [y* (adorn y_)]
                     [(ys* ...) (map adorn ys_)]]
         (with-syntax [[xe* (pt/rec/ctx x_ #'(λ (__) (ctx* (term-list (list . os*) (list 'begin (value->term __) y* ys* ...)))))]
                       [ye* (pt/eval (term-list os_ (cons 'begin (cons y_ ys_))))]]
           #'(begin xe* ye*)))]
      
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[os* os_]
                     [y* (adorn y_)]
                     [z* (adorn z_)]]
         (with-syntax [[x* (pt/rec/ctx x_ #'(λ (__) (ctx* (term-list (list . os*) (list 'if __ y* z*)))))]
                       [ry* (pt/eval y_)]
                       [rz* (pt/eval z_)]]
           #'(if x* ry* rz*)))]
      
      ; (lambda (v) x)
      [(term-list os_ (cons 'lambda rest))
       (pt/rec (term-list os_ (cons 'λ rest)))]
      
      ; (λ (v ...) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? vs_) ...)) x_))
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [os* os_]
                     [(vs* ...) vs_]]
         (with-syntax [[body* (pt/eval x_)]
                       [term* (if DISABLED #'null (adorn term_))]]
           #'(let [[fv* (λ (ctx*) (λ (vs* ...) body*))]]
               (Func term* ; for emitting
                     fv* ; for internal calls
                     (fv* unknown-ctx)))))] ; for external calls
      
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[os* os_]
                     [v* v_]]
         (with-syntax [[x* (pt/rec/ctx x_ #'(λ (__) (ctx* (term-list (list . os*) (list 'set! 'v* (value->term __))))))]]
           #'(set! v* x*)))]
      
      ; (f)
      [(term-list os_ (list f_))
       (with-syntax [[(fv* rv*) (generate-temporaries #'(f r))]
                     [os* os_]
                     [f* (adorn f_)]]
         (with-syntax [[f* (pt/rec/ctx f_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term __))))))]
                       [r* (pt/eval #'rv*)]]
           #'(let* [[fv* f*]
                    [rv* (call-func fv* ctx*)]]
               r*)))]
      
      ; (f x)
      [(term-list os_ (list f_ x_))
       (with-syntax [[(fv* xv* rv*) (generate-temporaries #'(f x r))]
                     [os* os_]
                     [f* (adorn f_)]
                     [x* (adorn x_)]]
         (with-syntax [[f* (pt/rec/ctx f_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term __) x*)))))]
                       [x* (pt/rec/ctx x_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term fv*) (value->term __))))))]
                       [r* (pt/eval #'rv*)]]
           #'(let* [[fv* f*]
                    [xv* x*]
                    [rv* (call-func fv* ctx* xv*)]]
               r*)))]
      
      ; (f x y)
      [(term-list os_ (list f_ x_ y_))
       (with-syntax [[(fv* xv* yv* rv*) (generate-temporaries #'(f x y r))]
                     [os* os_]
                     [f* (adorn f_)]
                     [x* (adorn x_)]
                     [y* (adorn y_)]]
         (with-syntax [[f* (pt/rec/ctx f_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term __) x* y*)))))]
                       [x* (pt/rec/ctx x_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term fv*) (value->term __) y*)))))] ;*
                       [y* (pt/rec/ctx y_ #'(λ (__) (ctx* (term-list (list . os*) (list (value->term fv*) (value->term xv*) __)))))]
                       [r* (pt/eval #'rv*)]]
           #'(let* [[fv* f*]
                    [xv* x*]
                    [yv* y*]
                    [rv* (call-func fv* ctx* xv* yv*)]]
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
  
  (define-syntax-rule (test-expand-term t)
    (syntax->datum ((term->racket (expand-term (make-term t))) emit)))
  
  (define (steps term emit)
    (eval (term emit)))
  
  (define-syntax-rule (test-eval t)
    (if NO_EMIT
        (macro-aware-eval* term->racket steps (make-term t) (λ _ (void)))
        (macro-aware-eval* term->racket steps (make-term t))))
  
  (define (my-external-function f)
    (f (f 17)))
  
  (define (string-first x)
    (substring x 0 1))
  
  (define (string-rest x)
    (substring x 1))
  
  (define plus (λ (x) (λ (y) (+ x y))))
  
  (define NO_EMIT #f)
  (define DISABLED #f)
  (set-debug-steps! #f)
  (set-debug-tags! #f)
  (set-debug-vars! #f)
)
