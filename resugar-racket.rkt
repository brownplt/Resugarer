(module resugar-racket racket
  (provide (all-defined-out))
  (require "utility.rkt")
  (require "resugar.rkt")
  (require profile)

  ; See debug-racket-3.rkt
  ; for a much cleaner presentation of the debugging approach.
  
  ; This code is OK to run in sequence; not so good concurrently.
  
  (define-struct Var (name value) #:transparent)
  (define-struct Func (func term)
    #:property prop:procedure
    (λ (self . args) (apply (Func-func self) args)))
  
  (define-setting SHOW_PROC_NAMES     set-show-proc-names!     #t)
  (define-setting DEBUG_VARS          set-debug-vars!          #f)
  (define-setting HIDE_EXTERNAL_CALLS set-hide-external-calls! #t)
  (define-setting DEBUG_STEPS         set-debug-steps!         #f)
  (define-setting DEBUG_TAGS          set-debug-tags!          #f)
  
  
  ;;; Keeping track of the stack ;;;
  
  (define $emit 'gremlin)
  (define $val 'gremlin)
  (define $stk (list))
  (define ($set-val! v)
    (set! $val v))
  
  (define ($push! x)
    (set! $stk (cons x $stk)))
    
  (define ($pop!)
    (set! $stk (cdr $stk)))
  
  (define ($reset!)
    (set! $stk (list)))
  
  
  ;;; Emitting Terms ;;;
  
  (define (reconstruct-stack x [stk $stk])
    (if (empty? stk)
        x
        (reconstruct-stack ((car stk) x) (cdr stk))))

  (define (display-skip t)
    (when DEBUG_STEPS
      (display (format "SKIP: ~a\n\n" (show-term t DEBUG_TAGS)))))
  
  (define (display-step t)
    (display (format "~a\n" (show-term t DEBUG_TAGS)))
    (when DEBUG_STEPS (newline)))
  
  (define (emit x)
    (let* [[t (value->term (reconstruct-stack x))]
           [u (unexpand-term t)]]
      (if (could-not-unexpand? u)
          (display-skip t)
          (display-step u))))
  
  (define (value->term x)
    (cond [(Func? x)
           (value->term (Func-term x))]
          [(term-list? x)
           (term-list (term-list-tags x) (map value->term (term-list-terms x)))]
          [(Var? x)
           (let* [[name (Var-name x)]
                  [term (value->term (Var-value x))]
                  [u    (unexpand-term term)]]
             (if DEBUG_VARS
                 (term-list (list) (list name ':= term))
                 (if (could-not-unexpand? u) name u)))]
          [(and SHOW_PROC_NAMES (procedure? x))
           (object-name x)]
          [else
           x]))
  
  ; Slow!
  (define ($emit-id v)
    (let* [[name (Var-name v)]
           [term (value->term (Var-value v))]
           [u (unexpand-term term)]]
      (if (could-not-unexpand? u) ($emit v) (void))))
  
  
  ;;; Annotating Racket Programs to Emit ;;;
  
  ; Top level
  (define (annotate-term term [emit emit])
    (set! $emit emit)
    (with-syntax [[t* (annot/eval term)]]
      #'(begin ($reset!)
               (let [[$result t*]]
                 ($emit $result)
                 $result))))
  
  ; Push a frame onto the stack (and pop it after)
  (define (annot/frame expr_ frame_)
    (with-syntax [[expr* expr_]
                  [frame* frame_]]
      #'(begin ($push! frame*)
               ($set-val! expr*)
               ($pop!)
               $val)))
  
  ; Annotate function argument expressions
  (define (annot/args xs_ os_ fv_ xvs0_ xvs_ xts_)
    (if (empty? xs_)
        empty
        (with-syntax [[os* os_]
                      [fv* fv_]
                      [(xvs0* ...) xvs0_]
                      [(xts* ...) (cdr xts_)]]
          (cons (annot/frame (annot/eval (car xs_))
                             #'(λ (__) (term-list (list . os*) (list fv* xvs0* ... __ xts* ...))))
                (annot/args (cdr xs_) os_ fv_ (append xvs0_ (list (car xvs_))) (cdr xvs_) (cdr xts_))))))
  
  ; Call external code
  (define (annot/extern-call func_ args_)
    (with-syntax [[func* func_]
                  [(args* ...) args_]]
      (annot/frame #'(func* args* ...)
                   #'(λ (__) (term-id (list (o-external)) __)))))
  
  ; Call a function, which may have been annotated or not.
  (define (annot/call func_ args_)
    (with-syntax [[func* func_]
                  [(args* ...) args_]
                  [extern-call* (annot/extern-call func_ args_)]]
      (if HIDE_EXTERNAL_CALLS
          #'(if (Func? func*)
                (func* args* ...)
                extern-call*)
          #'(func* args* ...))))

  (define-syntax-rule (stack-frame (hole origins) expr)
    (λ (hole) (term-list (list . origins) expr)))
  
  
  
  ; Prepare a term to be shown
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
      
      ; (f xs ...)
      [(term-list os_ (list f_ xs_ ...))
       (with-syntax [[os* os_]
                     [f* (adorn f_)]
                     [(xs* ...) (map adorn xs_)]]
         #'(term-list (list . os*) (list f* xs* ...)))]
      
      ; value c
      [c_
       (with-syntax [[c* c_]]
         (if (symbol? c_)
             #'(Var 'c* c*)
             #'c*))]))
  
  
  
  (define (annot/eval term_)
    (match term_
      
      [(term-id os_ x_)
       (with-syntax [[os* os_]
                     [x* (adorn x_)]]
         (annot/frame (annot/eval x_) #'(λ (__) (term-id (list . os*) x*))))]
      
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (annot/eval x_)]
      
      ; (begin x y ys ...)
      [(term-list os_ (list 'begin x_ y_ ys_ ...))
       (with-syntax [[os* os_]
                     [(yts* ...) (map adorn (cons y_ ys_))]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[x* (annot/frame (annot/eval x_)
                                        #'(λ (__) (term-list (list . os*) (list 'begin __ yts* ...))))]
                       [ys* (annot/eval (term-list os_ (cons 'begin (cons y_ ys_))))]]
           #'(let [[xv* x*]]
               ($emit (term-list (list . os*) (list 'begin xv* yts* ...)))
               ys*)))]
      
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[os* os_]
                     [yt* (adorn y_)]
                     [zt* (adorn z_)]
                     [y* (annot/eval y_)]
                     [z* (annot/eval z_)]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[test* (annot/frame (annot/eval x_)
                                           #'(λ (__) (term-list (list . os*) (list 'if __ yt* zt*))))]]
           #'(let [[xv* test*]]
               ($emit (term-list (list . os*) (list 'if xv* yt* zt*)))
               (if xv* y* z*))))]
      
      ; (lambda (v) x)
      [(term-list os_ (cons 'lambda rest))
       (annot/eval (term-list os_ (cons 'λ rest)))]
      
      ; (λ (v ...) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? vs_) ...)) x_))
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [os* os_]
                     [(vs* ...) vs_]]
         (with-syntax [[body* (annot/eval x_)]
                       [term* (adorn term_)]]
           #'(Func (λ (vs* ...) body*) term*)))]
      
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[os* os_]
                     [v* v_]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[x* (annot/frame (annot/eval x_)
                                        #'(λ (__) (term-list (list . os*) (list 'set! 'v* __))))]]
           #'(let [[xv* x*]]
               ($emit (term-list (list . os*) (list 'set! 'v* xv*)))
               (set! v* xv*))))]
      
      ; (f xs ...)
      [(term-list os_ (list f_ xs_ ...))
       (let [[xvs_ (map (λ (_) (with-syntax [[(v) (generate-temporaries #'(x))]] #'v)) xs_)]]
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [(xvs* ...) xvs_]
                     [os* os_]
                     [ft* (adorn f_)]
                     [(xts* ...) (map adorn xs_)]]
         (with-syntax [[f* (annot/frame (annot/eval f_)
                                        #'(λ (__) (term-list (list . os*) (list __ xts* ...))))]
                       [(xs* ...) (annot/args xs_ os_ #'fv* (list)
                                              xvs_ (syntax->datum #'(xts* ...)))]
                       [body* (annot/call #'fv* #'(xvs* ...))]]
           #'(let* [[fv* f*]
                    [xvs* xs*]
                    ...]
               ($emit (term-list (list . os*) (list fv* xvs* ...)))
               body*))))]
      
      ; value x
      [x_
       (with-syntax [[x* x_]]
         (if (symbol? x_)
             #'(begin ($emit-id (Var 'x* x*))
                      x*)
             #'x*))]
      ))
  
  (define-syntax-rule (test-term t)
    (syntax->datum (annotate-term (make-term t))))
  
  (define-syntax-rule (test-expand-term t)
    (syntax->datum (annotate-term (expand-term (make-term t)))))
  
  (define-syntax-rule (test-eval t)
    (eval (annotate-term (expand-term (make-term t))) (current-namespace)))
  
  (define-syntax-rule (test-silent-eval t)
    (eval (annotate-term (expand-term (make-term t)) (λ (x) (void))) (current-namespace)))
  
  (define (my-external-function f)
    (f (f 17)))
  
  (define (string-first x)
    (substring x 0 1))
  
  (define (string-rest x)
    (substring x 1))
)
