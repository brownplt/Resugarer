(module racket-stepper racket
  (provide (all-defined-out))
  ;(provide test-eval profile-eval test-term expand unexpand)
  (require "utility.rkt")
  (require profile)
  
  (define expand (make-parameter #f))
  (define unexpand (make-parameter #f))
  
  ; See debug-racket-3.rkt
  ; for a much cleaner presentation of the debugging approach.
  
  ; This code is OK to run in sequence; not so good concurrently.
  
  ; call/cc must be spelt call/cc, and not call-with-current-continuation
  
  (define-struct Var (name value) #:transparent)
  (define-struct Func (func term)
    #:property prop:procedure
    (λ (self . args) (apply (Func-func self) args)))
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
  
  (define (show-sexpr t [keep-tags #f])
    (define (convert t)
      (match t
        [(Tagged os t)
         (if keep-tags (Tagged os (convert t)) (convert t))]
        [(list ts ...)
         (map convert ts)]
        [t t]))
    (format "~a" (convert t)))
  
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
      (display (format "SKIP: ~a\n\n" (show-sexpr t DEBUG_TAGS)))))
  
  (define (display-step t)
    (display (format "~a\n" (show-sexpr t DEBUG_TAGS)))
    (when DEBUG_STEPS (newline)))
  
  (define (emit x [id #f])
    (if id
        (let* [[name (Var-name x)]
               [term (value->term (Var-value x))]
               [u ((unexpand) term)]]
          (if (CouldNotUnexpand? u) (emit x) (void)))
        (let* [[t (value->term (reconstruct-stack x))]
               [u ((unexpand) t)]]
          (if (CouldNotUnexpand? u)
              (display-skip t)
              (display-step u)))))
  
  (define (sugarless-emit x [id #f])
    (when (not id)
      (display (format "~a\n" (value->term (reconstruct-stack x))))))
  
  (define (value->term x)
    (match x
      [(Tagged os x)
       (Tagged os (value->term x))]
      [(Var name val)
       (let* [[term (value->term val)]
              [u ((unexpand) term)]]
         (if DEBUG_VARS
             (list name ':= term)
             (if (or (and HIDE_UNDEFINED (undefined? u))
                     (CouldNotUnexpand? u))
                 name u)))]
      [(Cont stk)
       (let [[stk (value->term (reconstruct-stack '__ stk))]]
         (list '*cont* (list stk)))]
      [(Func f t)
       (value->term t)]
      [(? (λ (x) (and SHOW_PROC_NAMES (procedure? x))) x)
       (or (object-name x) 'cont)]
      [(? list? x)
       (map value->term x)]
      [x x]))
  
  
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
  (define (annot/frame expr_ frame_)
    (with-syntax [[expr* expr_]
                  [frame* frame_]]
      #'(begin ($push! frame*)
               ($set-val! expr*)
               ($pop!)
               $val)))
  
  (define (annot/tagged os_ term_)
    (with-syntax [[(os* ...) os_]
                  [term* term_]]
      #'(Tagged (list os* ...) term*)))
  
  ; Annotate function argument expressions
  (define (annot/args xs_ fv_ xvs0_ xvs_ xts_)
    (if (empty? xs_)
        empty
        (with-syntax [[fv* fv_]
                      [(xvs0* ...) xvs0_]
                      [(xts* ...) (cdr xts_)]]
          (cons (annot/frame (annot/eval (car xs_))
                             #'(λ (__) (list fv* xvs0* ... __ xts* ...)))
                (annot/args (cdr xs_) fv_ (append xvs0_ (list (car xvs_))) (cdr xvs_) (cdr xts_))))))
  
  ; Call external code
  (define (annot/extern-call func_ args_)
    (with-syntax [[func* func_]
                  [(args* ...) args_]]
      (annot/frame #'(func* args* ...) #'(λ (__) (Tagged (list (Alien)) __)))))
  
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
      
      [(Tagged os_ x_)
       (with-syntax [[(os* ...) os_]
                     [x* (adorn x_)]]
         #'(Tagged (list os* ...) x*))]
      
      ; (begin x)
      [(list 'begin x_)
       (with-syntax [[x* (adorn x_)]]
         #'(list 'begin x*))]
      
      ; (begin x y ys ...)
      [(list 'begin x_ y_ ys_ ...)
       (with-syntax [[x* (adorn x_)]
                     [y* (adorn y_)]
                     [(ys* ...) (map adorn ys_)]]
         #'(list 'begin x* y* ys* ...))]
      
      ; (if x y z)
      [(list 'if x_ y_ z_)
       (with-syntax [[x* (adorn x_)]
                     [y* (adorn y_)]
                     [z* (adorn z_)]]
         #'(list 'if x* y* z*))]
      
      ; (λ (v ...) x)
      [(list 'lambda (list (? symbol? vs_) ...) x_)
       (with-syntax [[(vs* ...) vs_]
                     [x* (adorn x_)]]
         (with-syntax [[args* #'(list vs* ...)]]
           (with-syntax [[lambda* #'(list 'lambda args* x*)]]
             #'(let [[vs* 'vs*] ...]
                 lambda*))))]
      
      ; (define v x)
      [(list 'define (? symbol? v_) x_)
       (with-syntax [[v* v_]
                     [x* (adorn x_)]]
         #'(list 'define 'v* x*))]
      
      ; (define (f v ...) x)
      [(list 'define (list (? symbol? f_) (? symbol? vs_) ...) x_)
       (with-syntax [[f* f_]
                     [(vs* ...) vs_]
                     [x* (adorn x_)]]
         #'(list 'define (list 'f* 'vs* ...) x*))]
      
      ; (set! v x)
      [(list 'set (? symbol? v_) x_)
       (with-syntax [[v* v_]
                     [x* (adorn x_)]]
         #'(list 'set 'v* x*))]

      ; (f xs ...)
      [(list f_ xs_ ...)
       (with-syntax [[f* (adorn f_)]
                     [(xs* ...) (map adorn xs_)]]
         #'(list f* xs* ...))]
      
      ; value c
      [c_
       (with-syntax [[c* c_]]
         (if (symbol? c_)
             #'(Var 'c* c*)
             #'c*))]))
  
  (define (adorn/close x_ vs_)
    (with-syntax [[x* (adorn x_)]
                  [(vs* ...) vs_]]
      #'(let [[vs* 'vs*] ...] x*)))
  
  
  
  (define (annot/eval term_)
    (match term_
      
      [(Tagged os_ x_)
       (with-syntax [[x* (adorn (Tagged os_ x_))]]
         (annot/frame (annot/eval x_) #'(λ (__) x*)))]
      
      ; (begin x)
      [(list 'begin x_)
       (annot/eval x_)]
      
      ; (begin x y ys ...)
      [(list 'begin x_ y_ ys_ ...)
       (with-syntax [[(yts* ...) (map adorn (cons y_ ys_))]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[x* (annot/frame (annot/eval x_) #'(λ (__) (list 'begin __ yts* ...)))]
                       [ys* (annot/eval (cons 'begin (cons y_ ys_)))]
                       [term* #'(list 'begin xv* yts* ...)]]
           #'(let [[xv* x*]]
               ($emit term*)
               ys*)))]
      
      ; (if x y z)
      [(list 'if x_ y_ z_)
       (with-syntax [[yt* (adorn y_)]
                     [zt* (adorn z_)]
                     [y* (annot/eval y_)]
                     [z* (annot/eval z_)]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[test* (annot/frame (annot/eval x_) #'(λ (__) (list 'if __ yt* zt*)))]
                       [term* #'(list 'if xv* yt* zt*)]]
           #'(let [[xv* test*]]
               ($emit term*)
               (if xv* y* z*))))]
      
      ; (λ (v ...) x)
      [(list 'lambda (list (? symbol? vs_) ...) x_)
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [(vs* ...) vs_]]
         (with-syntax [[body* (annot/eval x_)]
                       [term* (adorn term_)]]
           #'(Func (λ (vs* ...) body*) term*)))]
      #|
      ; (define (f v ...) x)
      [(Node 'define (list (List (list (? symbol? f_) (? symbol? vs_) ...)) x_))
       (with-syntax [[f* f_]
                     [(vs* ...) vs_]
                     [xt* (adorn/close x_ vs_)]
                     [x* (annot/eval (Node 'λ (list (List vs_) x_)))]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[decl* #'(ListC 'f* 'vs* ...)]]
           (with-syntax [[term* #'(NodeC 'define decl* xt*)]]
             #'(define f*
                 (let [[xv* x*]]
                   ($emit term*)
                   xv*)))))]

      ; (define v x)
      [(Node 'define (list (? symbol? v_) x_))
       (with-syntax [[(xv*) (generate-temporaries #'(x))]
                     [v* v_]]
         (with-syntax [[x* (annot/frame (annot/eval x_) #'(λ (__) (NodeC 'define 'v* __)))]
                       [term* #'(NodeC 'define 'v* xv*)]]
           #'(define v*
               (let [[xv* x*]]
                 ($emit term*)
                 xv*))))]
      |#
      ; (set! v x)
      [(list 'set (? symbol? v_) x_)
       (with-syntax [[v* v_]
                     [(xv*) (generate-temporaries #'(x))]]
         (with-syntax [[x* (annot/frame (annot/eval x_) #'(λ (__) (list 'set 'v* __)))]
                       [term* #'(list 'set 'v* xv*)]]
           #'(let [[xv* x*]]
               ($emit term*)
               (set! v* xv*))))]

      ; (f xs ...)
      [(list f_ xs_ ...)
       (let [[xvs_ (map (λ (_) (with-syntax [[(v) (generate-temporaries #'(x))]] #'v)) xs_)]]
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [(xvs* ...) xvs_]
                     [ft* (adorn f_)]
                     [(xts* ...) (map adorn xs_)]]
         (with-syntax [[f* (annot/frame (annot/eval f_) #'(λ (__) (list __ xts* ...)))]
                       [(xs* ...) (annot/args xs_ #'fv* (list)
                                              xvs_ (syntax->datum #'(xts* ...)))]
                       [body* (annot/call #'fv* #'(xvs* ...))]
                       [term* #'(list fv* xvs* ...)]]
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
    (syntax->datum (annotate-terms (list 'ts ...))))
  
  (define-syntax-rule (test-expand ts ...)
    (syntax->datum (annotate-terms (list ((expand) 'ts) ...))))
  
  (define-syntax-rule (test-eval ts ...)
    (begin (newline)
           (eval (annotate-terms (list ((expand) 'ts) ...))
                 (current-namespace))))
  
  (define-syntax-rule (profile-eval t)
    (with-syntax [[prog* (annotate-term (expand (make-term t)) (λ x (void)))]]
      (eval #'(profile-thunk (λ () prog*)) (current-namespace))))

    
  (define (my-external-function f)
    (f (f 17)))
  
  (define (string-first x)
    (substring x 0 1))
  
  (define (string-rest x)
    (substring x 1))
  )