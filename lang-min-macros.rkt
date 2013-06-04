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


(define-macro thunk () ()
  [(thunk body)
   (lambda unused body)])

(define-macro force () ()
  [(force thunk)
   (apply thunk "unused")])

(define-macro let () ()
  [(let x e b)
   (apply (lambda x b) e)])

(define-macro or () (let)
  [(or x) x]
  [(or x xs ...)
   (apply (lambda t (if t t (or xs ...))) x)])
;   (let t x (if t t (or xs ...)))])

(define-macro letrec () (let)
  [(letrec x e b)
   (let x 0 (begin (set! x e) b))])

;(define-macro lets () (let)
;  [(lets [^ [^ x e] xs ...] b)
;   (let x e (lets [^ xs ...] b))]
;  [(lets [^] b)
;   b])

(define-macro lambdas () ()
  [(lambdas [^ var] body)
   (lambda var body)]
  [(lambdas [^ v1 v2 vs ...] body)
   (lambda v1 (lambdas [^ v2 vs ...] body))])

(define-macro lets () ()
  [(lets [^ [^ x e]] b)
   (apply (lambda x b) e)]
  [(lets [^ [^ x e] [^ xs es] ...] b)
   (apply (lambda x (lets [^ [^ xs es] ...] b)) e)])

(define-macro sets () ()
  [(sets [^ [^ x e]] b)
   (begin (set! x e) b)]
  [(sets [^ [^ x e] xs ...] b)
   (begin (set! x e) (sets [^ xs ...] b))])

(define-macro letrecs () (lets sets)
  [(letrecs [^ [^ x e] ...] b)
   (lets [^ [^ x 0] ...]
         (sets [^ [^ x e] ...]
               b))])

(define-macro cond (else) ()
  [(cond [^ else x])    x]
  [(cond [^ x y])       (if x y (+ 0 0))]
  [(cond [^ x y] z ...) (if x y (cond z ...))])

;(define-macro std-letrecs () (let lets thunk force)
;  [(std-letrec [^ [^ var init] ...] body)
;   (lets [^ [^ var 0] ...]
;         (lets [^ [^ var (let temp init (thunk (set! var temp)))] ...]
;               (let bod (thunk body)
;                 (begin (begin (force var) ...)
;                        (force bod)))))])

; TODO: bug!
(define-macro condfalse (else) (cond)
  [(condfalse)
   (cond [^ else #f])])

(define-macro process-state (->) (cond)
  [(_ "accept")
   (lambda stream
     (cond
       [^ (empty? stream) #t]
       [^ #t #f]))]
  [(_ [^ label -> target] ...)
   (lambda stream
     (cond
       [^ (empty? stream) #f]
       [^ (eq? label (first stream)) (apply target (rest stream))]
       ...
       [^ #t #f]))])

(define-macro automaton (:) (process-state letrecs)
  [(_ init-state
    [^ state : response ...]
    ...)
   (letrecs [^ [^ state (process-state response ...)] ...]
     init-state)])

(define-macro Cadavr () (letrecs cond)
  [(Cadavr input)
   (letrecs [^ [^ init (lambda x (cond [^ (empty? x)
                                          #f]
                                       [^ (eq? "c" (first x))
                                          (apply more (rest x))]))]
               [^ more (lambda x (cond [^ (empty? x)
                                          #f]
                                       [^ (eq? "a" (first x))
                                          (apply more (rest x))]
                                       [^ (eq? "d" (first x))
                                          (apply more (rest x))]
                                       [^ (eq? "r" (first x))
                                          (apply end (rest x))]))]
               [^ end (lambda x (cond [^ (empty? x)
                                         #t]
                                      [^ #t #f]))]]
     (apply init input))])

(define-macro Cadr () (letrecs cond)
  [(Cadr input)
   (letrecs [^ [^ init (lambda x #t)]]
     (apply init input))])

#|  Totally Bonkers |#

(define-macro engine-part (->) (cond)
  [(engine-part "accept")
   (lambda input #t)]
  [(engine-part [^ label -> target] ...)
   (lambda input
     (cond
       [^ (eq? input label) target]
       ...
       [^ #t #f]))])

(define-macro engine (:) (cond lambdas engine-part)
  [(engine [^ state : response ...] ...)
   (lambdas [^ s i]
     (cond [^ (eq? s state) (apply (engine-part response ...) i)]
           ...))])

(define-macro run () ()
  [(run fun engine state inputs)
   (apply fun engine state inputs)])

(define-macro run-body () (run lambdas cond let)
  [(run-body)
   (lambdas [^ eng state inputs]
      (let next (apply eng state (first inputs))
        (cond [^ (eq? next #f) #f]
              [^ (eq? next #t) #t]
              [^ #t (let inputs (rest inputs)
                      (run run-fun eng next inputs))])))])

(define-macro list () ()
  [(list) empty]
  [(list x xs ...) (cons x (list xs ...))])

(define-macro twiceevaled () ()
  [(twiceevaled x) 0]
  [(twiceevaled x y z ...)
   (apply (lambda w (twiceevaled x (+ z w) ...))
          (apply (lambda v x) y))])
;   (apply (lambda v x)
;   (letrec map (lambda f (lambda l
;                 (if (empty? l)
;                     empty
;                     (cons (apply f (first l))
;                           (apply map f (rest l))))))
;     (apply map (lambda v x) (list y ...)))])

;(test-eval (engine [^ "x" : "accept"]))
;(test-eval (run (engine [^ "x" : "accept"]) "x" empty))
;(test-eval (run (engine [^ "x" : "accept"]) "x" (cons "x" empty)))
;(test-eval (run (engine [^ "more" : [^ "a" -> "more"]]) "more"
;                (cons "a" (cons "a" (cons "a" empty)))))

(define-macro cpsM () (cpsT)
  [(cpsM ("lambda" x y))
   (lambda x (lambda k_ (cpsT y k_)))]
  [(cpsM x)
   x])

(define-macro cpsT () (cpsM)
  [(cpsT ("apply" x y) k)
   (cpsT x (lambda f_ (cpsT y (lambda e_ (apply f_ e_ k)))))]
  [(cpsT x k)
   (apply k (cpsM x))])

(define-macro cps () (cpsT cpsM)
  [(cps x) (cpsT x (lambda h_ h_))])

(define-macro cpsM* () (cpsC* cpsM*)
  [(cpsM* ("lambda" v e))
   (lambda v (lambda k (cpsC* e k)))]
  [(cpsM* x) x])

(define-macro cpsC* () (cpsC* cpsK* cpsM*)
  [(cpsC* ("lambda" v e) c)
   (apply c (cpsM* ("lambda" v e)))]
  [(cpsC* ("apply" f e) c)
   (cpsK* f (lambda f_ (cpsK* e (lambda e_ (apply f_ e_ c)))))]
  [(cpsC* x c)
   (apply c (cpsM* x))])

(define-macro cpsK* () (cpsK* cpsM*)
  [(cpsK* ("lambda" v e) k)
   (apply k (cpsM* ("lambda" v e)))]
  [(cpsK* ("apply" f e) k)
   (cpsK* f (lambda f_ (cpsK* e (lambda e_ (apply f_ e_ k)))))]
  [(cpsK* x c)
   (apply c (cpsM* x))])

(define-macro Fischer () ()
  [(Fischer ("lambda" x y))
   (lambda k (apply k
     (lambda x (lambda k (apply (Fischer y) (lambda m (apply k m)))))))]
  [(Fischer ("apply" x y))
   (lambda k (apply (Fischer x) (lambda m (apply (Fischer y)
     (lambda n (apply (apply m n) (lambda a (apply k a))))))))]
  [(Fischer x)
   (lambda k (apply k x))])

(test-eval
 (letrec run-fun
   (run-body)
   (lets [^ [^ an-engine
               (engine [^ "more" : [^ "a" -> "more"]])]
            [^ the-input
               (cons "a" (cons "a" (cons "a" empty)))]]
         (run run-fun an-engine "more" the-input))))

(set-debug-steps! #t)
(set-debug-tags! #t)
(set-debug-store! #f)

(test-eval (+ 1 2))
(test-eval (apply (lambda x (+ x 1)) (+ 1 2)))
(test-eval (let x 3 (+ x x)))
(test-eval (letrec x (lambda y x) (apply x 6)))
(test-eval (cond (^ #f (+ 1 2))))
(test-eval (lets [^ [^ x 1] [^ y 2]] (+ x y)))
(test-eval (letrecs [^ [^ x 1]] x))
(test-eval (letrecs [^ [^ x 1] [^ y 2]] (+ x y)))
(test-eval (cond [^ (empty? (cons 1 2)) 3] [^ #f 4] [^ else (+ 5 6)]))
(test-eval (or (eq? 1 2) (eq? 2 2) (eq? 3 2)))
(test-eval (twiceevaled (+ 1 2) 3 4))
(test-eval (cps ("apply" ("lambda" x (+ x 1)) 3)))
(test-eval (cpsT ("apply" ("apply" ("lambda" f ("lambda" x ("apply" f ("apply" f x))))
                                   ("lambda" x (+ x 1)))
                          (+ 1 2)) (lambda h h)))
(test-eval (cpsT ("apply" ("lambda" f ("apply" f 1)) ("lambda" x (+ x 1)))
                 (lambda h h)))
(test-eval (cpsK* ("apply" ("lambda" f ("apply" f 1)) ("lambda" x (+ x 1)))
                 (lambda h h)))

(test-eval (cons (Cadavr (cons "c" (cons "a" (cons "d" (cons "r" empty)))))
                 (Cadavr (cons "c" (cons "d" empty)))))

#|
(test-eval (apply (Fischer ("apply" ("lambda" x (+ x 1)) 3)) (lambda h h)))
(test-eval (apply (Fischer ("apply" ("apply" ("lambda" f ("lambda" x ("apply" f ("apply" f x))))
                                   ("lambda" x (+ x 1)))
                          (+ 1 2))) (lambda h h)))
|#
;(test-eval (std-letrecs [^ [^ x 1]] x))

#|
(test-eval
 (automaton
  init
  [^ init : "accept"]))

(test-eval
 (let M (automaton
         init
         [^ init : "accept"])
   (apply M empty)))

(test-eval
 (let M (automaton
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
 (let M (automaton
         init
         [^ init : [^ "a" -> init]])
   (apply M (cons "a" (cons "a" (cons "a" empty))))))
|#

;(test-trace (+ 1 2))
;(test-trace (letrec x x x))
;(test-trace (letrecs [^ [^ x (lambda z y)] [^ y (lambda z x)]]
;                     (apply x y)))
;(test-trace (cond [^ (empty? (cons 1 2)) 3] [^ #f 4] [^ else (+ 5 6)]))
;(test-trace (+ 1 (cond (^ (eq? 1 2) (+ 1 2)) (^ (eq? 1 3) (+ 3 4)))))
;(test-trace (lets [^ [^ x (+ 1 1)] [^ y (+ 1 2)]] (+ x y)))
;(test-trace (letrec x x (+ x x)))
;(test-trace (letrecs [^ [^ x (lambda z x)] [^ y (lambda z y)]] (apply x y)))