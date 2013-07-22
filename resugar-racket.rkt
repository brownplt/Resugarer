(module resugar-racket racket
  (provide (all-defined-out))
  (require "utility.rkt")
  (require "resugar.rkt")
  (require profile)

  ; See debug-racket-3.rkt
  ; for a much cleaner presentation of the debugging approach.
  
  ; This code is OK to run in sequence; not so good concurrently.
  
  ; call/cc must be spelt call/cc, and not call-with-current-continuation
  
  (define-struct Var (name value) #:transparent)
  (define-struct Func (func term)
    #:property prop:procedure
    (λ (self . args) (apply (Func-func self) args)))
  (define-struct term-list* (terms))
  (define-struct Cont (stk))
  (define undefined (letrec [[x x]] x))
  (define (undefined? x) (eq? x undefined))
  
  (define-setting SHOW_PROC_NAMES     set-show-proc-names!     #t)
  (define-setting SHOW_CONTINUATIONS  set-show-continuations!  #t)
  (define-setting DEBUG_VARS          set-debug-vars!          #f)
  (define-setting HIDE_EXTERNAL_CALLS set-hide-external-calls! #t)
  (define-setting DEBUG_STEPS         set-debug-steps!         #f)
  (define-setting DEBUG_TAGS          set-debug-tags!          #f)
  (define-setting HIDE_UNDEFINED      set-hide-undefined!      #t)
  
  
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
  
  (define ($reset! [stk (list)])
    (set! $stk stk))
  
  
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
  
  (define (emit x [id #f])
    (if id
        (let* [[name (Var-name x)]
               [term (value->term (Var-value x))]
               [u (unexpand-term term)]]
          (if (could-not-unexpand? u) (emit x) (void)))
        (let* [[t (value->term (reconstruct-stack x))]
               [u (unexpand-term t)]]
          (if (could-not-unexpand? u)
              (display-skip t)
              (display-step u)))))
  
  (define (value->term x)
    (cond [(Func? x)
           (value->term (Func-term x))]
          [(term-list*? x)
           (term-list (list) (map value->term (term-list*-terms x)))]
          [(term-list? x)
           (term-list (term-list-tags x) (map value->term (term-list-terms x)))]
          [(Var? x)
           (let* [[name (Var-name x)]
                  [term (value->term (Var-value x))]
                  [u    (unexpand-term term)]]
             (if DEBUG_VARS
                 (term-list (list) (list name ':= term))
                 (if (or (and HIDE_UNDEFINED (undefined? u))
                         (could-not-unexpand? u))
                     name u)))]
          [(Cont? x)
           (let [[stk (value->term (reconstruct-stack '__ (Cont-stk x)))]]
             (term-list (list) (list '*cont* stk)))]
          [(and SHOW_PROC_NAMES (procedure? x))
           (or (object-name x) 'cont)]
          [else
           x]))
  
  
  ;;; Annotating Racket Programs to Emit ;;;
  
  ; Top level
  (define (annotate-terms terms [emit emit])
    (set! $emit emit)
    (with-syntax [[(ts* ...) (map annot/eval terms)]]
      #'(begin ($reset!)
               (let [[$result (let [] ts* ...)]]
                 ($emit $result)
                 $result))))
  
  ; Push a frame onto the stack (and pop it after)
  (define (annot/frame expr_ os_ frame_)
    (with-syntax [[expr* expr_]
                  [frame* (make-frame os_ frame_)]]
      #;#'(begin ($push! frame*)
               (let [[$val expr*]]
                 ($pop!)
                 $val)) ; insignificant
      #'(begin ($push! frame*)
               ($set-val! expr*)
               ($pop!)
               $val)))
  
  (define (make-frame os_ body_)
    (with-syntax [[(os* ...) os_]
                  [body* body_]]
      (if (empty? os_)
          #'(λ (__) (term-list* body*))
          #'(λ (__) (term-list (list os* ...) body*)))))
  
  (define (annot/term os_ term_)
    (with-syntax [[(os* ...) os_]
                  [term* term_]]
      (if (empty? os_)
          #'(term-list* term*)
          #'(term-list (list os* ...) term*))))
  
  ; Annotate function argument expressions
  (define (annot/args xs_ os_ fv_ xvs0_ xvs_ xts_)
    (if (empty? xs_)
        empty
        (with-syntax [[fv* fv_]
                      [(xvs0* ...) xvs0_]
                      [(xts* ...) (cdr xts_)]]
          (cons (annot/frame (annot/eval (car xs_)) os_ #'(list fv* xvs0* ... __ xts* ...))
                (annot/args (cdr xs_) os_ fv_ (append xvs0_ (list (car xvs_))) (cdr xvs_) (cdr xts_))))))
  
  ; Call external code
  (define (annot/extern-call func_ args_)
    (with-syntax [[func* func_]
                  [(args* ...) args_]]
      (annot/frame #'(func* args* ...) (list (o-external)) #'__)))
  
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
  
  
  
  ; Prepare a term to be shown
  (define (adorn term_)
    (match term_
      
      [(term-id os_ x_)
       (annot/term os_ (adorn x_))]
      
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (with-syntax [[x* (adorn x_)]]
         (annot/term os_ #'(list 'begin x*)))]
      
      ; (begin x y ys ...)
      [(term-list os_ (list 'begin x_ y_ ys_ ...))
       (with-syntax [[x* (adorn x_)]
                     [y* (adorn y_)]
                     [(ys* ...) (map adorn ys_)]]
         (annot/term os_ #'(list 'begin x* y* ys* ...)))]
      
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[x* (adorn x_)]
                     [y* (adorn y_)]
                     [z* (adorn z_)]]
         (annot/term os_ #'(list 'if x* y* z*)))]
      
      ; (lambda (v ...) x)
      [(term-list os_ (cons 'lambda rest))
       (adorn (term-list os_ (cons 'λ rest)))]
      
      ; (λ (v ...) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? vs_) ...)) x_))
       (with-syntax [[(vs* ...) vs_]
                     [x* (adorn x_)]]
         (with-syntax [[args* (annot/term os2_ #'(list vs* ...))]]
           (with-syntax [[lambda* (annot/term os_ #'(list 'λ args* x*))]]
             #'(let [[vs* 'vs*] ...]
                 lambda*))))]
      
      ; (define v x)
      [(term-list os_ (list 'define (? symbol? v_) x_))
       (with-syntax [[v* v_]
                     [x* (adorn x_)]]
         (annot/term os_ #'(list 'define 'v* x*)))]
      
      ; (define (f v ...) x)
      [(term-list os_ (list 'define (term-list os2_ (list (? symbol? f_) (? symbol? vs_) ...)) x_))
       (with-syntax [[f* f_]
                     [(vs* ...) vs_]
                     [x* (adorn x_)]]
         (with-syntax [[decl* (annot/term os2_ #'(list 'f* 'vs* ...))]]
           (annot/term os_ #'(list 'define decl* x*))))]
      
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[v* v_]
                     [x* (adorn x_)]]
         (annot/term os_ #'(list 'set! 'v* x*)))]

      ; (f xs ...)
      [(term-list os_ (list f_ xs_ ...))
       (with-syntax [[f* (adorn f_)]
                     [(xs* ...) (map adorn xs_)]]
         (annot/term os_ #'(list f* xs* ...)))]
      
      ; value c
      [c_
       (with-syntax [[c* c_]]
         (if (symbol? c_)
             (if (symbol=? c_ '^)
                 #''^
                 #'(Var 'c* c*))
             #'c*))]))
  
  (define (adorn/close x_ vs_)
    (with-syntax [[x* (adorn x_)]
                  [(vs* ...) vs_]]
      #'(let [[vs* 'vs*] ...] x*)))
  
  
  
  (define (annot/eval term_)
    (match term_
      
      [(term-id os_ x_)
       (with-syntax [[x* (adorn x_)]]
         (annot/frame (annot/eval x_) os_ #'(list x*)))]
      
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (annot/eval x_)]
      
      ; (begin x y ys ...)
      [(term-list os_ (list 'begin x_ y_ ys_ ...))
       (with-syntax [[(yts* ...) (map adorn (cons y_ ys_))]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[x* (annot/frame (annot/eval x_) os_ #'(list 'begin __ yts* ...))]
                       [ys* (annot/eval (term-list os_ (cons 'begin (cons y_ ys_))))]
                       [term* (annot/term os_ #'(list 'begin xv* yts* ...))]]
           #'(let [[xv* x*]]
               ($emit term*)
               ys*)))]
      
      ; (if x y z)
      [(term-list os_ (list 'if x_ y_ z_))
       (with-syntax [[yt* (adorn y_)]
                     [zt* (adorn z_)]
                     [y* (annot/eval y_)]
                     [z* (annot/eval z_)]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[test* (annot/frame (annot/eval x_) os_ #'(list 'if __ yt* zt*))]
                       [term* (annot/term os_ #'(list 'if xv* yt* zt*))]]
           #'(let [[xv* test*]]
               ($emit term*)
               (if xv* y* z*))))]
      
      ; (lambda (v) x)
      [(term-list os_ (cons 'lambda rest))
       (annot/eval (term-list os_ (cons 'λ rest)))]
      
      ; (λ (v ...) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? vs_) ...)) x_))
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [(vs* ...) vs_]]
         (with-syntax [[body* (annot/eval x_)]
                       [term* (adorn term_)]]
           #'(Func (λ (vs* ...) body*) term*)))]
      
      ; (define (f v ...) x)
      [(term-list os_ (list 'define (term-list os2_ (list (? symbol? f_) (? symbol? vs_) ...)) x_))
       (with-syntax [[f* f_]
                     [(vs* ...) vs_]
                     [xt* (adorn/close x_ vs_)]
                     [x* (annot/eval (term-list os_ (list 'λ (term-list os2_ vs_) x_)))]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[decl* (annot/term os2_ #'(list 'f* 'vs* ...))]]
           (with-syntax [[term* (annot/term os_ #'(list 'define decl* xt*))]]
             #'(define f*
                 (let [[xv* x*]]
                   ($emit term*)
                   xv*)))))]

      ; (define v x)
      [(term-list os_ (list 'define (? symbol? v_) x_))
       (with-syntax [[(xv*) (generate-temporaries #'(x))]
                     [v* v_]]
         (with-syntax [[x* (annot/frame (annot/eval x_) os_ #'(list 'define 'v* __))]
                       [term* (annot/term os_ #'(list 'define 'v* xv*))]]
           #'(define v*
               (let [[xv* x*]]
                 ($emit term*)
                 xv*))))]
      
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[v* v_]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[x* (annot/frame (annot/eval x_) os_ #'(list 'set! 'v* __))]
                       [term* (annot/term os_ #'(list 'set! 'v* xv*))]]
           #'(let [[xv* x*]]
               ($emit term*)
               (set! v* xv*))))]

      ; (f xs ...)
      [(term-list os_ (list f_ xs_ ...))
       (let [[xvs_ (map (λ (_) (with-syntax [[(v) (generate-temporaries #'(x))]] #'v)) xs_)]]
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [(xvs* ...) xvs_]
                     [ft* (adorn f_)]
                     [(xts* ...) (map adorn xs_)]]
         (with-syntax [[f* (annot/frame (annot/eval f_) os_ #'(list __ xts* ...))]
                       [(xs* ...) (annot/args xs_ os_ #'fv* (list)
                                              xvs_ (syntax->datum #'(xts* ...)))]
                       [body* (annot/call #'fv* #'(xvs* ...))]
                       [term* (annot/term os_ #'(list fv* xvs* ...))]]
           #'(let* [[fv* f*]
                    [xvs* xs*]
                    ...]
               ($emit term*)
               body*))))]
      
      ; value x
      [x_
       (with-syntax [[x* x_]]
         (if (symbol? x_)
             #'(begin ($emit (Var 'x* x*) #t)
                      x*)
             #'x*))]
      ))
  
  (define (call/cc f)
    (let [[old-stk $stk]]
      (call-with-current-continuation
       (λ (k) (let [[cont (Func (λ args ($reset! old-stk) (apply k args))
                                (if SHOW_CONTINUATIONS
                                    (Cont old-stk)
                                    (gensym 'cont_)))]]
                (f cont))))))
  
  
  ;;; Testing ;;;
  
  (define-syntax-rule (test-term ts ...)
    (syntax->datum (annotate-terms (list (make-term ts) ...))))
  
  (define-syntax-rule (test-expand-term ts ...)
    (syntax->datum (annotate-terms (list (expand-term (make-term ts)) ...))))
  
  (define-syntax-rule (test-eval ts ...)
    (eval (annotate-terms (list (expand-term (make-term ts)) ...))
          (current-namespace)))
  
  (define-syntax-rule (test-silent-eval ts ...)
    (eval (annotate-terms (list (expand-term (make-term ts)) ...)
                          (λ x (void)))
          (current-namespace)))
  
  (define-syntax-rule (profile-silent-eval t)
    (with-syntax [[prog* (annotate-term (expand-term (make-term t)) (λ x (void)))]]
      (eval #'(profile-thunk (λ () prog*)) (current-namespace))))
  
  (define (my-external-function f)
    (f (f 17)))
  
  (define (string-first x)
    (substring x 0 1))
  
  (define (string-rest x)
    (substring x 1))
)
