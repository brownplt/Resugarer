#lang racket

(require redex)
(require "resugar-redex.rkt")
(require "lang-min.rkt")


(define-macro Let
  [(Let [^ [^ x e]] b)
   (apply (lambda x b) e)]
  [(Let [^ [^ x e] y ys ...] b)
   (apply (lambda x (! Let [^ y ys ...] b)) e)])

(define-macro Let1
  [(Let1 x e b)
   (apply (lambda x b) e)])

(define-macro Letrec
  [(Letrec [^ [^ x e] ...] b)
   (Let [^ [^ x 0] ...]
        (begin (set! x e) ... b))])

(define-macro Cond
  [(Cond [^ $else x])   (begin x)] ; begin required so that a step is shown!
  [(Cond [^ x y])       (if x y (+ 0 0))]
  [(Cond [^ x y] z zs ...) (if x y (! Cond z zs ...))])

(define-macro ProcessState
  [(_ "accept")
   (lambda stream
     (Cond
       [^ (eq? "" stream) #t]
       [^ $else (begin #f)]))]
  [(_ [^ label $-> targets ...] ...)
   (lambda stream
     (if (eq? "" stream) #f
         (Let [^ [^ head (string-first stream)]
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
   (Letrec [^ [^ state (ProcessState response ...)] ...]
     (lambda x (! apply init-state x)))])

;;;;;;;;;;;;;;;;;;;;;;;;;;


#;(test-trace (+ 1 (Cond (^ (eq? 1 2) (+ 1 2)) (^ (eq? 1 3) (+ 3 4)))))

(test-trace
 (Let1 M (Automaton
         init
         [^ init $: [^ "c" $-> more]]
         [^ more $: [^ "a" $-> more]
                    [^ "d" $-> more]
                    [^ "r" $-> end init]]
         [^ end $:  "accept"])
   (apply M "carcadr")))
