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
                          (pair? t)
                          (null? t)
                          (void? t)))
  
  (define (term->racket term)
    (λ (c) (pt/eval empty-ctx term c)))
  
  (define (pt/eval ctx term c_)
    (let [[expr (pt/rec ctx term c_)]]
      (with-syntax [[ctx* ctx]
                    [expr* expr]
                    [c* c_]
                    [term* term]]
        #'(begin
            ;(emit ctx* (fully-unwrap-term term*) c*)
            (let [[result expr*]]
              (emit ctx* (unwrap-term result) c*)
              (unwrap-value result))))))
  
  (define (tlist os . ts)
    (term-list os ts))
  
  (define (pt/rec ctx term c_)
    (match term
      ; (term-id x)
      [(term-id os_ x_)
       (with-syntax [[ctx* ctx] [os* os_]]
         (with-syntax [[x* (pt/eval #'(λ (w) (ctx* (term-id (list . os*) w))) x_ c_)]]
           #'x*))]
      ; (begin x)
      [(term-list os_ (list 'begin x_))
       (pt/eval ctx x_ c_)]
       ;(with-syntax [[x* (pt/eval ctx x_ c_)]]
       ;  #'x*)]
      ; (begin x y)
      [(term-list os_ (list 'begin x_ ys_))
       (with-syntax [[(x-var*) (generate-temporaries #'(x))]
                     [ctx* ctx] [os* os_] [ys* ys_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) 'begin w ys*))) x_ c_)]
                       [ys-eval* (pt/eval ctx (term-list os_ (list 'begin ys_)) c_)]]
           #'(let [[x-var* x-eval*]]
               ys-eval*)))]
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
      [(term-list os_ (list 'λ (term-list os2_ (list (? symbol? v_))) x_))
       (with-syntax [[(ctx-var*) (generate-temporaries #'(ctx))]
                     [term* term]]
         (with-syntax [[x-eval* (pt/eval #'ctx-var* x_ c_)]
                       [v* v_]]
           #'(Lamb (λ (ctx-var*) (λ (v*) (Var 'v* x-eval*))) term*)))]
      ; (set! v x)
      [(term-list os_ (list 'set! (? symbol? v_) x_))
       (with-syntax [[ctx* ctx] [os* os_] [v* v_]]
         (with-syntax [[x-eval* (pt/eval #'(λ (w) (ctx* (tlist (list . os*) 'set! 'v* w))) x_ c_)]]
           #'(set! v* x-eval*)))]
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
  
  (define (unwrap-var v)
    (let* [[name (Var-name v)]
           [term (unwrap-term (Var-value v))]
           [u (unexpand-term term)]]
      (if (could-not-unexpand? u) name u)))
  
  (define (unwrap-term x)
    (match x
      [(? Lamb? x) (Lamb-term x)]
      [(? Var? x) (unwrap-var x)]
      [(? atomic? x) x]))
  
  (define (fully-unwrap-term x)
    (match x
      [(term-list os ts)
       (term-list os (map fully-unwrap-term ts))]
      [(term-id os t)
       (term-id os (fully-unwrap-term t))]
      [(? Lamb? x) (fully-unwrap-term (Lamb-term x))]
      [(? Var? x) (fully-unwrap-term (unwrap-var x))]
      [(? atomic? x) x]))
  
  (define-syntax-rule (test-term t)
    ((term->racket (make-term t)) (λ (x) (display (format "~a\n" x)))))
  
  (define (steps term emit)
    (eval (term emit)))
  
  (define-syntax-rule (test-eval t)
    (macro-aware-eval* term->racket steps (make-term t)))

  (define-macro Cond
    [(Cond [^ $else x])   x]
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
  
  (define-macro Set
    [(Set [^ [^ [^ f x] e]] b)
     (begin (set! f (lambda (x) e)) b)]
    [(Set [^ [^ [^ f x] e] xs ...] b)
     (begin (set! f (lambda (x) e)) (Set [^ xs ...] b))]
    [(Set [^ [^ x e]] b)
     (begin (set! x e) b)]
    [(Set [^ [^ x e] xs ...] b)
     (begin (set! x e) (Set [^ xs ...] b))])

  (define-macro Letrec
    [(Letrec [^ [^ x e] ...] b)
     (Let [^ [^ x 0] ...]
          (Set [^ [^ x e] ...]
               b))])
  
  (define-macro Or
    [(Or x) x]
    [(Or x y ys ...)
     ((λ (t) (if t t (Or y ys ...))) x)])
  
  (define-macro And
    [(And x) (begin x)]
    [(And x y ys ...)
     (if x (And y ys ...) #f)])
  
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
     (Letrec [^ [^ [^ init x]
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "c" head) (! more tail)]
                                  [^ $else #f])))]
                [^ [^ more x]
                   (if (equal? x "") #f
                       (Let [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (equal? "a" head) (! more tail)]
                                  [^ (equal? "d" head) (! more tail)]
                                  [^ (equal? "r" head) (! end tail)]
                                  [^ $else #f])))]
                [^ [^ end x]
                   (equal? x "")]]
             (! init input))])
  
  (set-debug-steps! #f)
  (set-debug-tags! #f)
  
  (test-eval 3)
  (test-term (+ 1 2))
  (test-eval (+ 1 2))
  (test-eval (+ (+ 1 2) (+ 3 4)))
  (test-eval (if #t (+ 1 2) (+ 3 4)))
  (test-eval (λ (x) x))
  (test-eval ((λ (x) (+ x 1)) 3))
  
  (test-eval (+ 0 (car (cons (+ 1 2) (+ 3 4)))))
  (test-eval (Let [^ [^ x 1] [^ y (+ 1 2)]] (+ x y)))
  (test-eval (Or #f (+ 1 2)))
  (test-eval (Inc (+ 1 2)))
  (test-eval (Inc (+ (Inc 1) (Inc 2))))
  (test-eval (+ 1 (Cond [^ #f (+ 1 2)] [^ (Or #f #t) (+ 2 3)])))
  (test-eval ((λ (x) (if (set! x (+ x 1)) x x)) 3))
  (test-eval ((λ (x) (begin (set! x (+ x 1)) (+ x 1))) 3))
  (test-eval (Letrec [^ [^ [^ is-even? n] (! Or (zero? n) (! is-odd? (sub1 n)))]
                        [^ [^ is-odd? n] (! And (not (zero? n)) (! is-even? (sub1 n)))]]
                     (is-odd? 11)))
  (test-eval (begin (+ 1 2) (+ 3 4)))
  (test-eval ((λ (f) (begin (set! f (λ (x) x)) (f 4))) 3))
  (test-eval (Cdavr "cadr"))
  (test-eval (Cdavr "cdad"))
  (test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
  ;(test-eval (((λ (f) (λ (x) (f (f x)))) (λ (x) (+ x 1))) (+ 2 3)))
  ;(test-eval ((lambda (s) (Let [^ [^ x (string-first s)] [^ y (string-rest s)]] y)) "abc"))
  ;(test-eval ((λ (x) (x x)) (λ (x) x)))
)
