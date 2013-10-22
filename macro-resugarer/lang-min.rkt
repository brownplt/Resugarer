(module lang-min racket
  (provide
   Min red
   test-eval test-expand
   test-trace
   )

; Assembled from Matthias' letrec (personal correspondence)
; and redex/example/letrex.rkt.
; The language is probably mostly correct.

(require rackunit)
(require redex)
(require "resugar-redex.rkt")


  ;;;;;;;;;;;;;;;;
  ;;; Language ;;;
  ;;;;;;;;;;;;;;;;

(define-language Min
  (p (top s e))
  (e (apply o e ...)
     (op o e ...)
     (set! o x e)
     (begin o e e ...)
     (if o e e e)
     (rec o x e)
     x
     v
     (x := e))
  (op + cons first rest empty? eq? string-first string-rest)
  (s (store (x x v) ...))
  (v (lambda o x e)
     number
     boolean
     string
     empty
     (cons o v v))
  (x variable-not-otherwise-mentioned)
  (pc (top (store (x x v) ...) ec))
  (ec (apply o v ... ec e ...)
      (op o v ... ec e ...)
      (set! o variable ec)
      (begin o ec e e ...)
      (if o ec e e)
      hole)
  (o (origins any)))

(define-metafunction Min
  swap : x x any -> any
  [(swap x_1 x_2 x_1) x_2]
  [(swap x_1 x_2 x_2) x_1]
  [(swap x_1 x_2 (any_1 ...)) ((swap x_1 x_2 any_1) ...)]
  [(swap x_1 x_2 any_1) any_1])

(define-metafunction Min
  subs : x e e -> e
  [(subs x_1 e_1 (lambda o x_1 e_2))
   (lambda o x_1 e_2)]
  [(subs x_1 e_1 (lambda o x_2 e_2))
   ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
              (term (lambda o x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]
  [(subs x_1 e_1 (set! o x_2 e_2))
   (set! o (subs x_1 e_1 x_2) (subs x_1 e_1 e_2))]
  [(subs x_1 e_1 (rec o x_2 e_2))
   ,(term-let ([x_new (variable-not-in (term e_1) (term x_2))])
              (term (rec o x_new (subs x_1 e_1 (swap x_2 x_new e_2)))))]  
  [(subs x_1 e_1 x_1) e_1]
  [(subs x_1 e_1 x_2) x_2]
  [(subs x_1 e_1 (apply o e_2 ...))
   (apply o (subs x_1 e_1 e_2) ...)]
  [(subs x e number) number]
  [(subs x e (name a boolean)) a]
  [(subs x e (name a string)) a]
  [(subs x e (if o e_1 e_2 e_3))
   (if o (subs x e e_1) (subs x e e_2) (subs x e e_3))]
  [(subs x e (begin o e_1 ...))
   (begin o (subs x e e_1) ...)]
  [(subs x e (op o e_1 ...))
   (op o (subs x e e_1) ...)]
  [(subs x e (cons o e_1 e_2))
   (cons o (subs x e e_1) (subs x e e_2))]
  [(subs x e empty) empty])

(define-metafunction Min
  look : x (store (x x v) ...) -> v
  [(look x (store (x_1 x_11 v_1) ... (x x_10 v) (x_2 x_12 v_2) ...))
   v
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define-metafunction Min
  set : x v (store (x x v) ...) -> (store (x x v) ...)
  [(set x v_new (store (x_1 x_11 v_1) ... (x x_10 v) (x_2 x_12 v_2) ...))
   (store (x_1 x_11 v_1) ... (x x_10 v_new) (x_2 x_12 v_2) ...)
   (side-condition (not (member (term x) (term (x_1 ...)))))])

(define (string-first str)
  (substring str 0 1))
(define (string-rest str)
  (substring str 1))
  
(define red
  (reduction-relation
   Min
   (--> (in-hole pc_1 (begin o v e_1 e_2 ...))
        (in-hole pc_1 (begin o e_1 e_2 ...))
        "begin-many")
   
   (--> (in-hole pc_1 (begin o e_1))
        (in-hole pc_1 e_1)
        "begin-one")
 
   (--> (in-hole pc (empty? o empty))               (in-hole pc #t))
   (--> (in-hole pc (empty? o (cons o_1 v_1 v_2)))  (in-hole pc #f))
   (--> (in-hole pc (+ o v ...))                    (in-hole pc ,(apply + (term (v ...)))))
   (--> (in-hole pc (eq? o v_1 v_2))                (in-hole pc ,(equal? (term v_1) (term v_2))))
   (--> (in-hole pc (first o_1 (cons o_2 v_1 v_2))) (in-hole pc v_1))
   (--> (in-hole pc (rest o_1 (cons o_2 v_1 v_2)))  (in-hole pc v_2))
   (--> (in-hole pc (string-first o v))             (in-hole pc ,(string-first (term v))))
   (--> (in-hole pc (string-rest o v))              (in-hole pc ,(string-rest (term v))))
   
   (--> (top s (in-hole ec x))
        (top s (in-hole ec (look x s)))
        "variable")
   
   (--> (top s           (in-hole ec (set! o_2 x v)))
        (top (set x v s) (in-hole ec v))
        "set!")

   (--> (top (store (x_1 x_2 v_1) ...)
             (in-hole ec (apply o_1 (lambda o_2 x e) v)))
        (top (store (x_1 x_2 v_1) ... (x_new x v))
             (in-hole ec (subs x x_new e)))
        (fresh x_new)
        "apply-one")

   (--> (top (store (x_1 x_2 v_1) ...)
             (in-hole ec (apply o_1 (lambda o_2 x e) v_2 v_3 v_4 ...)))
        (top (store (x_1 x_2 v_1) ... (x_new x v_2))
             (in-hole ec (apply o_1 (subs x x_new e) v_3 v_4 ...)))
        (where x_new ,(variable-not-in (term (x_1 ...)) 'x))
        "apply-many")
   
   (--> (in-hole pc (if o #t e_1 e_2))
        (in-hole pc e_1)
        "if-true")
  
   (--> (in-hole pc (if o #f e_1 e_2))
        (in-hole pc e_2)
        "if-false")))

   ;with [(--> a ,(collect (term b))) (==> a b)]))


  ;;;;;;;;;;;;;;;;;;;;;;;;
  ;;; Language Testing ;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;

(define (run-eval e)
  (third (car (apply-reduction-relation* red `(top (store) ,e)))))

(define o '(origins ()))

(define-syntax-rule
  (eval-tests [actual expected] ...)
  (begin (check-equal? (run-eval actual) expected) ...))

(eval-tests
 [`(apply ,o (lambda ,o x x) 3) 3]
 [`(+ ,o 2 3) 5]
 [`(eq? ,o "a" "a") #t]
 [`(eq? ,o "a" "b") #f]
 [`(empty? ,o empty) #t]
 [`(empty? ,o (cons ,o "a" "b")) #f]
 [`(cons ,o (+ ,o 1 2) (+ ,o 3 4)) `(cons ,o 3 7)]
 [`(+ ,o (+ ,o 1 2) (+ ,o 3 4)) 10]
 [`(rest ,o (first ,o (cons ,o (cons ,o "a" (cons ,o "b" empty)) "c")))
  `(cons ,o "b" empty)]
 [`(apply ,o (lambda ,o x (begin ,o (set! ,o x 1) x)) 3)    1]
 [`(apply ,o (lambda ,o x (apply ,o (lambda ,o x x) 2)) 1)  2]
 [`(apply ,o (lambda ,o x (+ ,o x 1)) (+ ,o 1 2))           4]
 [`(apply ,o (lambda ,o x (lambda ,o y (+ ,o x y))) 2 3)    5]
 [`(apply ,o (lambda ,o x (begin ,o
     (set! ,o x (+ ,o x 1))
     (set! ,o x (apply ,o (lambda ,o x (begin ,o (set! ,o x (+ ,o x 2)) (+ ,o x x))) x))
     (+ ,o x x x)))
   7)                                                      60]
 [`(begin ,o (+ ,o 1 2) (+ ,o 3 4) (+ ,o 5 6))             11]
 [`(if ,o #t 1 2) 1]
 [`(if ,o #f 1 2) 2]
 [`(string-first ,o "abc") "a"]
 [`(string-rest ,o "abc") "bc"]
 )
  
;;; Resugaring Integration ;;;

(define empty-store (term (store)))

(define (join expr store)
  `(top ,store ,expr))

(define (split top)
  (let [[store (second top)]
        [expr (third top)]]
    (cons expr store)))

(define (lookup-var var store)
  (define (lookup var bindings)
    (match bindings
      [(list) #f]
      [(cons (list x name v) bindings)
       (if (symbol=? var x) (cons name v) (lookup var bindings))]))
  (lookup var (cdr store)))

(define MAMin
  (make-redex-language "Min" Min red join split lookup-var))

(define (flatten-eval-tree tree)
  (if (empty? (cdr tree))
      (list (car tree))
      (cons (car tree) (flatten-eval-tree (second tree)))))

(define-syntax-rule (test-eval t)
  (begin
    (for-each (λ (x) (display (format "~a\n" x)))
              (flatten-eval-tree
               (macro-aware-eval MAMin (make-term t) empty-store)))
    (display "\n")))

(define-syntax-rule (make-redex-term t)
  (term->redex (expand-term (make-term t))))

(define (nondeterm-step tree)
  (display tree) (newline)
  (if (empty? (cdr tree))
      #f
      (cdr tree)))
  
(define (determ-step tree)
  (if (empty? (cdr tree))
      #f
      (cadr tree)))
  
(define marred
  (reduction-relation Min
    (--> p ,(macro-aware-redex-step MAMin (term p) 1))
    (--> p ,(macro-aware-redex-step MAMin (term p) 2))
    (--> p ,(macro-aware-redex-step MAMin (term p) 3))))

(define-syntax-rule (test-trace t)
  (macro-aware-traces MAMin marred (join (make-redex-term t) empty-store)))

(define-syntax-rule (test-expand t)
  (show-term (expand-term (make-term t))))

)