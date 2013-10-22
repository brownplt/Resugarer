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

; * Sometimes a macro RHS must be wrapped in 'begin' for two reasons:
;   - So that it's reduction shows as a step (otherwise, e.g. (or (+ 1 2)) -> 3)
;   - So that a calling macro doesn't inadvertently tag a constant.


(define-macro Thunk
  [(Thunk body)
   (lambda unused body)])

(define-macro Force
  [(Force thunk)
   (apply thunk "unused")])

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
         (begin (set! x e) ... b))])

(define-macro Cond
  [(Cond [^ $else x])   (begin x)] ; begin required so that a step is shown!
  [(Cond [^ x y])       (if x y (+ 0 0))]
  [(Cond [^ x y] z zs ...) (if x y (! Cond z zs ...))])

(define-macro AmbCond
  [(AmbCond [^ $else x])      (begin x)]
  [(AmbCond [^ x y])          (if x y (+ 0 0))]
  [(AmbCond [^ x y] z zs ...) (if x (amb y (! AmbCond z zs ...))
                                    (! AmbCond z zs ...))])

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
       [^ $else (begin #f)]))]
  [(_ [^ label $-> targets ...] ...)
   (lambda stream
     (if (eq? "" stream) #f
         (Lets [^ [^ head (string-first stream)]
                  [^ tail (string-rest stream)]]
               (Cond
                [^ (eq? label head)
                   (amb (! apply targets tail) ...)]
                ...
                [^ $else #f]))))])

(define-macro Automaton
  [(_ init-state
    [^ state $: response ...]
    ...)
   (Letrecs [^ [^ state (ProcessState response ...)] ...]
     (lambda x (! apply init-state x)))])
;     init-state)])

(define-macro List
  [(List) empty]
  [(List x xs ...) (cons x (List xs ...))])

(define-macro TwiceEvaled
  [(TwiceEvaled x) 0]
  [(TwiceEvaled x y z ...)
   (apply (lambda w (TwiceEvaled x (+ z w) ...))
          (apply (lambda v x) y))])

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
(test-eval (Letrecs [^ [^ y (+ x 1)] [^ x 1]] (+ x y)))
(test-eval
 (Let M (Automaton
         init
         [^ init $: [^ "c" $-> more]]
         [^ more $: [^ "a" $-> more]
                    [^ "d" $-> more]
                    [^ "r" $-> end]]
         [^ end $:  "accept"])
   (apply M "cadr")))
(test-trace
 (Let M (Automaton
         init
         [^ init $: [^ "c" $-> more]]
         [^ more $: [^ "a" $-> more]
                    [^ "d" $-> more]
                    [^ "r" $-> end init]]
         [^ end $:  "accept"])
   (apply M "carcadr")))
#;(test-eval
 (Let M (Automaton
         init
         [^ init $: [^ "c" $-> more]]
         [^ more $: [^ "a" $-> more]
                    [^ "d" $-> more]
                    [^ "r" $-> end]]
         [^ end $:  "accept"])
   (apply M "cdad")))

#;(test-trace (amb (+ 1 2) (+ 3 4) (+ 5 6)))
#;(test-trace (AmbCond [^ #t (+ 1 2)]
                     [^ #f (+ 3 4)]
                     [^ #t (+ 5 6)]))

;(test-eval (Letrecs [^ [^ f (λ n (if (eq? n 0) 77 (apply f (! + 0 0))))]]
;                    (apply f (+ 1 2))))

;(test-eval (std-Letrecs [^ [^ x 1]] x))


;(test-trace (Let x 1 x))
;(test-trace (+ (+ 1 2) (+ 3 4)))
;(test-trace (+ 1 2))
;(test-trace (Letrec x x x))
;(test-trace (Letrecs [^ [^ x (lambda z y)] [^ y (lambda z x)]]
;                     (apply x y)))
;(test-trace (Cond [^ (empty? (cons 1 2)) 3] [^ #f 4] [^ else (+ 5 6)]))
;(test-trace (+ 1 (Cond (^ (eq? 1 2) (+ 1 2)) (^ (eq? 1 3) (+ 3 4)))))
;(test-trace (Lets [^ [^ x (+ 1 1)] [^ y (+ 1 2)]] (+ x y)))
;(test-trace (Letrec x x (+ x x)))
;(test-trace (Letrecs [^ [^ x (lambda z x)] [^ y (lambda z y)]] (apply x y)))