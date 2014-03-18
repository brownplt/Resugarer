#lang racket

(require redex)
(require "resugar-redex.rkt")
(require "lang-min.rkt")

(set-debug-steps! #f)


(define-macro Lets
  [(Lets [^ [^ x e]] b)
   (apply (lambda x b) e)]
  [(Lets [^ [^ x e] y ys ...] b)
   (apply (lambda x (! Lets [^ y ys ...] b)) e)])

(define-macro Let
  [(Let x e b)
   (apply (lambda x b) e)])

(define-macro Letrec
  [(Letrec [^ [^ x e] ...] b)
   (Lets [^ [^ x 0] ...]
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
  [(_ [^ label $-> target] ...)
   (lambda stream
     (if (eq? "" stream) #f
         (Lets [^ [^ head (string-first stream)]
                 [^ tail (string-rest stream)]]
              (Cond
               [^ (eq? label head)
                  (! apply target tail)]
               ...
               [^ $else (begin #f)]))))])

(define-macro Automaton
  [(_ init-state
    [^ state $: response ...]
    ...)
   (Letrec [^ [^ state (ProcessState response ...)] ...]
     (lambda x (! apply init-state x)))])

;;;;;;;;;;;;;;;;;;;;;;;;;;


#;(test-trace (+ 1 (Cond (^ (eq? 1 2) (+ 1 2)) (^ (eq? 1 3) (+ 3 4)))))

(test-trace
 (Let M (Automaton
         init
         [^ init $: [^ "c" $-> more]]
         [^ more $: [^ "a" $-> more]
                    [^ "d" $-> more]
                    [^ "r" $-> end]]
         [^ end $:  "accept"])
   (apply M "cadr")))
