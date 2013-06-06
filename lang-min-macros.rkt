#lang racket

(require redex)
(require "resugar-redex.rkt")
(require "lang-min.rkt")

  ;;;;;;;;;;;;;;
  ;;; Macros ;;;
  ;;;;;;;;;;;;;;

; Examples:
; * cond         DONE
; * let          DONE
; * letrec       DONE?
; * automata     DONE?
; * cps          NOT DONE
; * var lifting  NOT DONE
; * traffic/elevator/nonpl


(define-macro Thunk
  [(Thunk body)
   (lambda unused body)])

(define-macro Force
  [(Force Thunk)
   (apply Thunk "unused")])

(define-macro Let
  [(Let x e b)
   (apply (lambda x b) e)])

(define-macro Or
  [(Or x) x]
  [(Or x xs ...)
   (apply (lambda t (if t t (Or xs ...))) x)])
;   (Let t x (if t t (Or xs ...)))])

(define-macro Letrec
  [(Letrec x e b)
   (Let x 0 (begin (set! x e) b))])

;(define-macro Lets () (Let)
;  [(Lets [^ [^ x e] xs ...] b)
;   (Let x e (Lets [^ xs ...] b))]
;  [(Lets [^] b)
;   b])

(define-macro Lambdas
  [(Lambdas [^ var] body)
   (lambda var body)]
  [(Lambdas [^ v1 v2 vs ...] body)
   (lambda v1 (Lambdas [^ v2 vs ...] body))])

(define-macro Lets
  [(Lets [^ [^ [^ f x] e]] b)
   (apply (lambda f b) (lambda x e))]
  [(Lets [^ [^ [^ f x] e] [^ xs es] ...] b)
   (apply (lambda f (Lets [^ [^ xs es] ...] b)) (lambda x e))]
  [(Lets [^ [^ x e]] b)
   (apply (lambda x b) e)]
  [(Lets [^ [^ x e] [^ xs es] ...] b)
   (apply (lambda x (Lets [^ [^ xs es] ...] b)) e)])

(define-macro Sets
  [(Sets [^ [^ [^ f x] e]] b)
   (begin (set! f (lambda x e)) b)]
  [(Sets [^ [^ [^ f x] e] xs ...] b)
   (begin (set! f (lambda x e)) (Sets [^ xs ...] b))]
  [(Sets [^ [^ x e]] b)
   (begin (set! x e) b)]
  [(Sets [^ [^ x e] xs ...] b)
   (begin (set! x e) (Sets [^ xs ...] b))])

(define-macro Letrecs
  [(Letrecs [^ [^ x e] ...] b)
   (Lets [^ [^ x 0] ...]
         (Sets [^ [^ x e] ...]
               b))])

(define-macro Cond
  [(Cond [^ $else x])    x]
  [(Cond [^ x y])       (if x y (+ 0 0))]
  [(Cond [^ x y] z ...) (if x y (Cond z ...))])

;(define-macro std-Letrecs () (Let Lets Thunk Force)
;  [(std-Letrec [^ [^ var init] ...] body)
;   (Lets [^ [^ var 0] ...]
;         (Lets [^ [^ var (Let temp init (Thunk (set! var temp)))] ...]
;               (Let bod (Thunk body)
;                 (begin (begin (Force var) ...)
;                        (Force bod)))))])

; TODO: bug!
(define-macro Condfalse 
  [(Condfalse)
   (Cond [^ $else #f])])

(define-macro ProcessState
  [(_ "accept")
   (lambda stream
     (Cond
       [^ (empty? stream) #t]
       [^ #t #f]))]
  [(_ [^ label $-> target] ...)
   (lambda stream
     (Cond
       [^ (empty? stream) #f]
       [^ (eq? label (first stream)) (apply target (rest stream))]
       ...
       [^ #t #f]))])

(define-macro Automaton
  [(_ init-state
    [^ state $: response ...]
    ...)
   (Letrecs [^ [^ state (ProcessState response ...)] ...]
     init-state)])

#|  Totally Bonkers |#

(define-macro EnginePart
  [(EnginePart "accept")
   (lambda input #t)]
  [(EnginePart [^ label $-> target] ...)
   (lambda input
     (Cond
       [^ (eq? input label) target]
       ...
       [^ #t #f]))])

(define-macro Engine
  [(Engine [^ state $: response ...] ...)
   (Lambdas [^ s i]
     (Cond [^ (eq? s state) (apply (EnginePart response ...) i)]
           ...))])

(define-macro Run
  [(Run fun Engine state inputs)
   (apply fun Engine state inputs)])

(define-macro RunBody 
  [(RunBody)
   (Lambdas [^ eng state inputs]
      (Let next (apply eng state (first inputs))
        (Cond [^ (eq? next #f) #f]
              [^ (eq? next #t) #t]
              [^ #t (Let inputs (rest inputs)
                      (run run-fun eng next inputs))])))])

(define-macro List
  [(List) empty]
  [(List x xs ...) (cons x (List xs ...))])

(define-macro TwiceEvaled
  [(TwiceEvaled x) 0]
  [(TwiceEvaled x y z ...)
   (apply (lambda w (TwiceEvaled x (+ z w) ...))
          (apply (lambda v x) y))])
;   (apply (lambda v x)
;   (Letrec map (lambda f (lambda l
;                 (if (empty? l)
;                     empty
;                     (cons (apply f (first l))
;                           (apply map f (rest l))))))
;     (apply map (lambda v x) (list y ...)))])

;(test-eval (Engine [^ "x" : "accept"]))
;(test-eval (run (Engine [^ "x" : "accept"]) "x" empty))
;(test-eval (run (Engine [^ "x" : "accept"]) "x" (cons "x" empty)))
;(test-eval (run (Engine [^ "more" : [^ "a" -> "more"]]) "more"
;                (cons "a" (cons "a" (cons "a" empty)))))

(define-macro CpsM
  [(CpsM ("lambda" x y))
   (lambda x (lambda k_ (CpsT y k_)))]
  [(CpsM x)
   x])

(define-macro CpsT
  [(CpsT ("apply" x y) k)
   (CpsT x (lambda f_ (CpsT y (lambda e_ (apply f_ e_ k)))))]
  [(CpsT x k)
   (apply k (CpsM x))])

(define-macro Cps
  [(Cps x) (CpsT x (lambda h_ h_))])

(define-macro CpsM*
  [(CpsM* ("lambda" v e))
   (lambda v (lambda k (CpsC* e k)))]
  [(CpsM* x) x])

(define-macro CpsC*
  [(CpsC* ("lambda" v e) c)
   (apply c (CpsM* ("lambda" v e)))]
  [(CpsC* ("apply" f e) c)
   (CpsK* f (lambda f_ (CpsK* e (lambda e_ (apply f_ e_ c)))))]
  [(CpsC* x c)
   (apply c (CpsM* x))])

(define-macro CpsK*
  [(CpsK* ("lambda" v e) k)
   (apply k (CpsM* ("lambda" v e)))]
  [(CpsK* ("apply" f e) k)
   (CpsK* f (lambda f_ (CpsK* e (lambda e_ (apply f_ e_ k)))))]
  [(CpsK* x c)
   (apply c (CpsM* x))])

(define-macro Fischer
  [(Fischer ("lambda" x y))
   (lambda k (apply k
     (lambda x (lambda k (apply (Fischer y) (lambda m (apply k m)))))))]
  [(Fischer ("apply" x y))
   (lambda k (apply (Fischer x) (lambda m (apply (Fischer y)
     (lambda n (apply (apply m n) (lambda a (apply k a))))))))]
  [(Fischer x)
   (lambda k (apply k x))])

(define-macro Cdavr
  [(Cdavr input)
   (Letrecs [^ [^ [^ init x]
                  (if (eq? x "") #f
                      (Lets [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (eq? "c" head) (! apply more tail)]
                                  [^ $else #f])))]
               [^ [^ more x]
                  (if (eq? x "") #f
                      (Lets [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (eq? "a" head) (! apply more tail)]
                                  [^ (eq? "d" head) (! apply more tail)]
                                  [^ (eq? "r" head) (! apply end tail)]
                                  [^ $else #f])))]
               [^ [^ end x]
                  (eq? x "")]]
     (! apply init input))])

(test-eval
 (Letrec run-fun
   (RunBody)
   (Lets [^ [^ an-Engine
               (Engine [^ "more" $: [^ "a" $-> "more"]])]
            [^ the-input
               (cons "a" (cons "a" (cons "a" empty)))]]
         (run run-fun an-Engine "more" the-input))))

(set-debug-steps! #f)
(set-debug-tags! #t)
(set-debug-store! #t)

(test-eval (+ 1 2))
(test-eval (apply (lambda x (+ x 1)) (+ 1 2)))
(test-eval (Let x 3 (+ x x)))
(test-eval (Letrec x (lambda y x) (apply x 6)))
(test-eval (Cond (^ #f (+ 1 2))))
(test-eval (Lets [^ [^ x 1] [^ y 2]] (+ x y)))
(test-eval (Letrecs [^ [^ x 1]] x))
(test-eval (Letrecs [^ [^ x 1] [^ y 2]] (+ x y)))
(test-eval (Cond [^ (empty? (cons 1 2)) 3] [^ #f 4] [^ $else (+ 5 6)]))
(test-eval (Or (eq? 1 2) (eq? 2 2) (eq? 3 2)))
(test-eval (Lets [^ [^ [^ f x] (+ x 1)]] (apply f 3)))
;(test-eval (Cps ("apply" ("lambda" x (+ x 1)) 3)))
;(test-eval (CpsT ("apply" ("apply" ("lambda" f ("lambda" x ("apply" f ("apply" f x))))
;                                   ("lambda" x (+ x 1)))
;                          (+ 1 2)) (lambda h h)))
;(test-eval (CpsT ("apply" ("lambda" f ("apply" f 1)) ("lambda" x (+ x 1)))
;                 (lambda h h)))
;(test-eval (CpsK* ("apply" ("lambda" f ("apply" f 1)) ("lambda" x (+ x 1)))
;                 (lambda h h)))

;(test-eval (Cdavr "cd"))
;(test-eval (Cdavr "cadr"))
(test-eval (Cdavr "cadr"))
(test-eval (Cdavr "cdad"))

#|
(test-eval (apply (Fischer ("apply" ("lambda" x (+ x 1)) 3)) (lambda h h)))
(test-eval (apply (Fischer ("apply" ("apply" ("lambda" f ("lambda" x ("apply" f ("apply" f x))))
                                   ("lambda" x (+ x 1)))
                          (+ 1 2))) (lambda h h)))
|#
;(test-eval (std-Letrecs [^ [^ x 1]] x))

#|
(test-eval
 (Automaton
  init
  [^ init : "accept"]))

(test-eval
 (Let M (Automaton
         init
         [^ init : "accept"])
   (apply M empty)))

(test-eval
 (Let M (Automaton
         init
         [^ init : [^ "c" -> more]]
         [^ more : [^ "a" -> more]
                   [^ "d" -> more]
                   [^ "r" -> end]]
         [^ end :  "accept"])
   (cons
    (apply M (cons "c" (cons "a" (cons "d" (cons "r" empty)))))
    (apply M (cons "c" (cons "d" empty))))))

(test-eval
 (Let M (Automaton
         init
         [^ init : [^ "a" -> init]])
   (apply M (cons "a" (cons "a" (cons "a" empty))))))
|#

;(test-trace (+ 1 2))
;(test-trace (Letrec x x x))
;(test-trace (Letrecs [^ [^ x (lambda z y)] [^ y (lambda z x)]]
;                     (apply x y)))
;(test-trace (Cond [^ (empty? (cons 1 2)) 3] [^ #f 4] [^ else (+ 5 6)]))
;(test-trace (+ 1 (Cond (^ (eq? 1 2) (+ 1 2)) (^ (eq? 1 3) (+ 3 4)))))
;(test-trace (Lets [^ [^ x (+ 1 1)] [^ y (+ 1 2)]] (+ x y)))
;(test-trace (Letrec x x (+ x x)))
;(test-trace (Letrecs [^ [^ x (lambda z x)] [^ y (lambda z y)]] (apply x y)))