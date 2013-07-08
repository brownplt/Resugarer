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
; * automata     DONE
; * cps          NOT DONE
; * var lifting  NOT DONE
; * traffic/elevator/nonpl

; Bugs:
; * Sometimes a macro RHS must be wrapped in 'begin' for two reasons:
;   - So that it's reduction shows as a step (otherwise, e.g. (or (+ 1 2)) -> 3)
;   - So that a calling macro doesn't inadvertently tag a constant.


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
  [(Or x) (begin x)]
  [(Or x y ys ...)
   (Let t x (if t t (! Or y ys ...)))])

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
  [(Lets [^ [^ x e]] b)
   (apply (lambda x b) e)]
  [(Lets [^ [^ x e] y ys ...] b)
   (apply (lambda x (! Lets [^ y ys ...] b)) e)])

(define-macro Sets
  [(Sets [^ [^ x e]] b)
   (begin (set! x e) b)]
  [(Sets [^ [^ x e] y ys ...] b)
   (begin (set! x e) (! Sets [^ y ys ...] b))])

(define-macro Letrecs
  [(Letrecs [^ [^ x e] ...] b)
   (Lets [^ [^ x 0] ...]
         (Sets [^ [^ x e] ...]
               b))])

(define-macro Cond
  [(Cond [^ $else x])   (begin x)] ; begin required so that a step is shown!
  [(Cond [^ x y])       (if x y (+ 0 0))]
  [(Cond [^ x y] z zs ...) (if x y (! Cond z zs ...))])

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
       [^ (eq? "" stream) #t]
       [^ $else #f]))]
  [(_ [^ label $-> target] ...)
   (lambda stream
     (if (eq? "" stream) #f
         (Lets [^ [^ head (string-first stream)]
                  [^ tail (string-rest stream)]]
               (Cond
                [^ (eq? label head) (! apply target tail)]
                ...
                [^ $else #f]))))])

(define-macro Automaton
  [(_ init-state
    [^ state $: response ...]
    ...)
   (Letrecs [^ [^ state (ProcessState response ...)] ...]
     init-state)])

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

(define-macro Cdavr
  [(Cdavr input)
   (Letrecs [^ [^ init (λ x
                  (if (eq? x "") #f
                      (Lets [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (eq? "c" head) (! apply more tail)]
                                  [^ $else #f]))))]
               [^ more (λ x
                  (if (eq? x "") #f
                      (Lets [^ [^ head (string-first x)]
                               [^ tail (string-rest x)]]
                            (Cond [^ (eq? "a" head) (! apply more tail)]
                                  [^ (eq? "d" head) (! apply more tail)]
                                  [^ (eq? "r" head) (! apply end tail)]
                                  [^ $else #f]))))]
               [^ end (λ x
                  (eq? x ""))]]
     (! apply init input))])

#;(test-eval
 (Letrec run-fun
   (RunBody)
   (Lets [^ [^ an-Engine
               (Engine [^ "more" $: [^ "a" $-> "more"]])]
            [^ the-input
               (cons "a" (cons "a" (cons "a" empty)))]]
         (run run-fun an-Engine "more" the-input))))

(set-debug-steps! #f)
(set-debug-tags! #f)

(test-eval (+ 1 2))
(test-eval (apply (lambda x (+ x 1)) (+ 1 2)))
(test-eval (Let x 3 (+ x x)))
(test-eval (Letrec x (lambda y x) (apply x 6)))
(test-eval (Cond (^ #f (+ 1 2))))
(test-eval (Lets [^ [^ x 1] [^ y 2]] (+ x y)))
(test-eval (Letrecs [^ [^ x 1]] x))
(test-eval (Letrecs [^ [^ x 1] [^ y 2]] (+ x y)))
(test-eval (Cond [^ (empty? (cons 1 2)) 3] [^ #f 4] [^ $else (+ 5 6)]))
(test-eval (+ 1 (Cond [^ #f (+ 1 2)] [^ (Or #f #t) (+ 2 3)])))
(test-eval (Or (eq? 1 2) (eq? 2 2) (eq? 3 2)))
(test-eval (Lets [^ [^ f (λ x (+ x 1))]] (apply f 3)))
(test-eval (Cdavr "cadr"))
(test-eval (Cdavr "cdad"))
(test-eval (Letrecs [^ [^ y x] [^ x 1]] (+ x y)))
(test-eval
 (Let M (Automaton
         init
         [^ init $: [^ "c" $-> more]]
         [^ more $: [^ "a" $-> more]
                    [^ "d" $-> more]
                    [^ "r" $-> end]]
         [^ end $:  "accept"])
   (apply M "cadr")))
(test-eval
 (Let M (Automaton
         init
         [^ init $: [^ "c" $-> more]]
         [^ more $: [^ "a" $-> more]
                    [^ "d" $-> more]
                    [^ "r" $-> end]]
         [^ end $:  "accept"])
   (apply M "cdad")))

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