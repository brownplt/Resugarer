(module resugar-racket racket
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
                 (if (could-not-unexpand? u) name u)))]
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
      
      ; (λ (v1 v2) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? v1_) (? symbol? v2_))) x_))
       (with-syntax [[os* os_]
                     [os2* os2_]
                     [v1* v1_]
                     [v2* v2_]
                     [x* (adorn x_)]]
         #'(let [[v1* 'v1*] [v2* 'v2*]]
             (term-list (list . os*) (list 'λ (term-list (list . os2*) (list v1* v2*)) x*))))]
      
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
      
      ; (begin x y)
      [(term-list os_ (list 'begin x_ y_))
       (with-syntax [[os* os_]
                     [y* (adorn y_)]]
         (with-syntax [[xe* (pt/rec/ctx x_ #'(λ (__) (ctx* (term-list (list . os*) (list 'begin (value->term __) y*)))))]
                       [ye* (pt/eval (term-list os_ (list 'begin y_)))]]
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
      
      ; (λ (v) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? v_))) x_))
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [os* os_]
                     [v* v_]]
         (with-syntax [[body* (pt/eval x_)]
                       [term* (if DISABLED #'null (adorn term_))]]
           #'(let [[fv* (λ (ctx*) (λ (v*) body*))]] ;*
               (Func term* ; for emitting
                     fv* ; for internal calls
                     (fv* unknown-ctx)))))] ; for external calls
      
      ; (λ (v1 v2) x)
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? v1_) (? symbol? v2_))) x_))
       (with-syntax [[(fv*) (generate-temporaries #'(f))]
                     [os* os_]
                     [v1* v1_]
                     [v2* v2_]]
         (with-syntax [[body* (pt/eval x_)]
                       [term* (if DISABLED #'null (adorn term_))]]
           #'(let [[fv* (λ (ctx*) (λ (v1* v2*) body*))]]
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

  (define-macro Cond
    [(Cond [^ $else x])   (begin x)]
    [(Cond [^ x y])       (if x y (void))]
    [(Cond [^ x y] z zs ...) (if x y (! Cond z zs ...))])
  
  (define-macro Let
;    [(Let [^ [^ [^ f x ...] e]] b)
;     ((lambda (f) b) (lambda (x ...) e))]
;    [(Let [^ [^ [^ f x ...] e] [^ xs es] ...] b)
;     ((lambda (f) (! Let [^ [^ xs es] ...] b)) (lambda (x ...) e))]
    [(Let [^ [^ x e]] b)
     ((lambda (x) b) e)]
    [(Let [^ [^ x e] y ys ...] b)
     ((lambda (x) (! Let [^ y ys ...] b)) e)])
  
  (define-macro Let1
    [(Let1 v x y)
     (Let [^ [^ v x]] y)])
  
  (define-macro Set
;    [(Set [^ [^ [^ f x ...] e]] b)
;     (begin (set! f (lambda (x ...) e)) b)]
;    [(Set [^ [^ [^ f x ...] e] xs ...] b)
;     (begin (set! f (lambda (x ...) e)) (! Set [^ xs ...] b))]
    [(Set [^ [^ x e]] b)
     (begin (set! x e) b)]
    [(Set [^ [^ x e] y ys ...] b)
     (begin (set! x e) (! Set [^ y ys ...] b))])

  (define-macro Letrec
    [(Letrec [^ [^ x e] ...] b)
     (Let [^ [^ x 0] ...]
          (Set [^ [^ x e] ...]
               b))])
  
  (define-macro Or
    [(Or x) (begin x)]
    [(Or x y ys ...)
     (Let [^ [^ t x]] (if t t (! Or y ys ...)))])
  
  (define-macro Or2
    [(Or2 x y) (Let1 t x (if t t y))])
  
  (define-macro And
    [(And x) (begin x)]
    [(And x y ys ...)
     (if x (! And y ys ...) #f)])
  
  (define-macro NotWellFormed
    [(NotWellFormed x) y])
  
  (define-macro Quickand
    [(Quickand x #t) x]
    [(Quickand #t y) y])
  
  (define-macro Just
    [(Just x) (begin x)])
  
  (define-macro M1
    [(M1 $emm) 3])
  
  (define-macro M2
    [(M2 x) (M1 x)])
  
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
     (Letrec [^ [^ init (λ (x)
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "c" head) (! more tail)]
                                  [^ $else (begin #f)]))))]
                [^ more (λ (x)
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "a" head) (! more tail)]
                                  [^ (equal? "d" head) (! more tail)]
                                  [^ (equal? "r" head) (! end tail)]
                                  [^ $else (begin #f)]))))]
                [^ end (λ (x)
                   (equal? x ""))]]
             (! init input))])
  
  (define-macro ProcessState
    [(_ "accept")
     (lambda (stream)
       (Cond
        [^ (equal? "" stream) #t]
        [^ $else #f]))]
    [(_ [^ label $-> target] ...)
     (lambda (stream)
       (if (equal? "" stream) #f
           (Let [^ [^ head (string-first stream)]
                   [^ tail (string-rest stream)]]
                (Cond
                 [^ (equal? label head) (! target (string-rest stream))]
                 ...
                 [^ $else (begin #f)]))))])

  (define-macro Automaton
    [(_ init-state
        [^ state $: response ...]
        ...)
     (Letrec [^ [^ state (ProcessState response ...)] ...]
             (λ (x) (! init-state x)))]) ; if just init-state, you don't see the application (init-state input)
  
  (define (time-fib)
    (display "Fibonacci:\n")
    (time (letrec ((fib (λ (n) (if (or (eq? n 0) (eq? n 1))
                                   1
                                   (+ (fib (- n 1)) (fib (- n 2)))))))
            (begin (fib 20) (void))))
    (time (test-eval (Letrec [^ [^ [^ fib n] (if (Or (eq? n 0) (eq? n 1))
                                                 1
                                                 (+ (fib (- n 1)) (fib (- n 2))))]]
                             (begin (fib 20) (void))))))
  
  (define (time-factorial)
    (display "Factorial:\n")
    (time (letrec ((factorial (λ (n) (if (eq? n 0)
                                         1
                                         (* n (factorial (- n 1)))))))
            (begin (factorial 10000) (void))))
    (time (test-eval (Letrec [^ [^ [^ factorial n] (if (eq? n 0)
                                                       1
                                                       (* n (factorial (- n 1))))]]
                             (begin (factorial 10000) (void))))))
  
  (define (time-fast-factorial)
    (display "Accumulating Factorial:\n")
    (time (letrec ((factorial (λ (n prod)
                                (if (eq? n 0) prod
                                    (factorial (- n 1) (* n prod))))))
            (begin (factorial 10000 1) (void))))
    (time (test-eval (Letrec [^ [^ [^ factorial n prod]
                                   (if (eq? n 0) prod (factorial (- n 1) (* n prod)))]]
                             (begin (factorial 10000 1) (void))))))
  
  (define NO_EMIT #f)
  (define DISABLED #f)
  (set-debug-steps! #f)
  (set-debug-tags! #f)
  (set-debug-vars! #f)
  
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
  (test-eval (Or 1 2))
  (test-eval (Or (And #f #t) (+ 1 2)))
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
  (test-eval (Letrec [^ [^ f (λ (n) (g n))] [^ g (λ (n) (+ n 1))]] (f 3)))
  (test-eval (Or (zero? 3) (sub1 3)))
  (test-eval (And (not (zero? 3)) (sub1 3)))
  (test-eval (! + 1 2))
  (test-eval (Letrec [^ [^ f (λ (n) (if (zero? n) 77 (f (+ 0 0))))]] (f (+ 0 0))))
  
  (test-eval (Letrec [^ [^ is-even? (λ (n) (Or (zero? n) (is-odd? (sub1 n))))]
                        [^ is-odd? (λ (n) (And (not (zero? n)) (is-even? (sub1 n))))]]
                     (is-odd? 11)))
  (test-eval (Let [^ [^ f (λ (x) (+ x 1))]] (f 3)))
  (test-eval (begin (+ 1 2) (+ 3 4)))
  (test-eval ((λ (f) (begin (set! f (λ (x) x)) (f 4))) 3))
  
  (test-eval (Cdavr "cdad"))
  (test-eval (Cdavr "cadr"))
  ;(test-expand-term (Cdavr "cadr")) ; Huge!
  ; You see (m "cadr") instead of (init "cadr") for the same reason
  ;   (Let [[x (λ (v) v)]] (Let [[y x]] (Let [[z y]] (z 0))))
  ; steps through (z 0) -> ((λ (v) v) 0) -> 0
  ; instead of    (z 0) -> (y 0) -> (x 0) -> ((λ (v) v) 0) -> 0
  ; steps through (+ 1 2), but never through (+ (+ 0 1) 2).
  (test-eval
   (Let [^ [^ m (Automaton
                 init
                 [^ init $: [^ "c" $-> more]]
                 [^ more $: [^ "a" $-> more]
                            [^ "d" $-> more]
                            [^ "r" $-> end]]
                 [^ end $:  "accept"])]]
        (m "cadr")))
  (test-eval
   (Let [^ [^ m (Automaton
                 init
                 [^ init $: [^ "c" $-> more]]
                 [^ more $: [^ "a" $-> more]
                            [^ "d" $-> more]
                            [^ "r" $-> end]]
                 [^ end $:  "accept"])]]
        (m "cdad")))
  (test-eval
   (Let [^ [^ m (Automaton
                 init
                 [^ init   $: [^ "1" $-> more-1]]
                 [^ more-1 $: [^ "0" $-> more-0]
                              [^ "1" $-> more-1]
                              [^ "." $-> end]]
                 [^ more-0 $: [^ "0" $-> more-0]
                              [^ "1" $-> more-1]]
                 [^ end    $: "accept"])]]
        (m "11010.")))
  ;(test-expand-term (Let [^ [^ x 1]] (+ x 1)))
  ;(time-fast-factorial)
  ;(time-fib)
  ;(time-factorial)
  #|
  (profile-thunk (λ () (test-eval (Letrec [^ [^ [^ fib n] (if (Or (eq? n 0) (eq? n 1))
                                               1
                                               (+ (fib (- n 1)) (fib (- n 2))))]]
                           (fib 22)))))
  (test-expand-term (Let [^ [^ x 1]] (+ x 1)))
  
  (test-expand-term (Letrec [^ [^ [^ fib n] (if (Or (eq? n 0) (eq? n 1))
                                               1
                                               (+ (fib (- n 1)) (fib (- n 2))))]]
                           (fib 15)))
|#
  ;(test-eval (M2 $emm)) BUG! I don't know how to fix this w/o ugly hacks
  #|
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
