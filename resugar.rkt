(module resugar racket
  (require (except-in rackunit fail))
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  (provide
   define-macro
   make-term test-expand term-list term-list? term-list-tags term-list-terms term-id
   expand-term unexpand-term show-term term->sexpr strip-term-tags
   could-not-unexpand?
   language language-name language-expr->term language-term->expr language-step language-show-expr
   macro-aware-step
   macro-aware-eval
   macro-aware-eval*)
   ;set-debug-tags! set-debug-steps! debug set-debug!)
  
  (define DEBUG_TAGS #f)
  (define (set-debug-tags! x) (set! DEBUG_TAGS x))
  (define DEBUG_STEPS #f)
  (define (set-debug-steps! x) (set! DEBUG_STEPS x))
  
  #|
     A language is free to work over whatever sort of exprs and contexts it wants.
     It must take evaluation steps over (expr, context) pairs.
     Contexts are hidden and do not get unexpanded.
     term->expr and expr->term *must* be inverses of each other,
       or else the semantic properties of the stepper are lost.

     Language expr ctx {
       name :: string
       term->expr :: term -> expr
       expr->term :: expr -> ctx -> term
       step :: expr -> ctx -> list (cons expr ctx)
       eval :: 
       show-expr :: expr -> ctx -> string      ; for debugging
     }
 
                                 init-ctx
                                    ↓
     pattern  ===>  term  --->  (expr, ctx)
                                    ↓
     pattern  <===  term  <---  (expr, ctx)
                                    ↓
                                   ...
     (===> expansion/unexpansion)
     (---> just pairing/unpairing and term<->expr conversion)
     (↓    evaluation step)
  |#
  
  (struct language
    (name term->expr expr->term step eval show-expr))
  
  (define-syntax-rule (test-expand t)
    (expand-term (make-term t)))
  
  (define-syntax-rule (expand-term t)
    (pattern->term (expand-pattern (term->pattern t))))
  
  (struct could-not-unexpand ()); because unexpand can return #f, which is a valid term :-(
  (define-syntax-rule (unexpand-term t)
    (let [[q (unexpand-pattern (term->pattern t))]]
      (if q (pattern->term q) (could-not-unexpand))))
  
  (define last-line #f)
  (define (output-line str)
    (when (not (equal? str last-line))
      (begin
        (display str)
        (newline)
        (when DEBUG_STEPS (newline))
        (set! last-line str))))
    
  (define (show-step t)
    (output-line (if DEBUG_TAGS
                     (show-term t #t)
                     (show-term t))))
    
  (define (show-skip t)
    (when DEBUG_STEPS
      (output-line (format "SKIP: ~a" (if DEBUG_TAGS
                                          (format "~v\n" (term->pattern t))
                                          (show-term t))))))
  
  ; macro-aware-step :: Language t c -> term -> c -> list (cons term c)
  (define (macro-aware-step lang t ctx)
    (let [[expr->term (language-expr->term lang)]
          [term->expr (language-term->expr lang)]
          [show-expr (language-show-expr lang)]
          [step (language-step lang)]]
      
      (when DEBUG_STEPS
        (show-step t))
      
      (define (catmap f xs)
        (append* (map f xs)))
      
      (define (new-step e ctx)
        (catmap resugar (step e ctx)))
      
      (define (resugar prog)
        (let* [[e (car prog)]
               [ctx (cdr prog)]
               [t (expr->term e ctx)]
               [p (unexpand-pattern (term->pattern t))]]
          (if p
              (list (cons (pattern->term p) ctx))
              (begin (when DEBUG_STEPS (show-skip e #;ctx))
                     (new-step e ctx)))))
      
      (new-step (term->expr (expand-term t)) ctx)))
  
  ; macro-aware-eval :: Language t c -> term -> c -> list (cons term c)
  (define (macro-aware-eval lang t ctx)
    (define (rec lang t ctx)
      (let [[next-progs (macro-aware-step lang t ctx)]
            [show-expr (language-show-expr lang)]
            [term->expr (language-term->expr lang)]]
        (cons (show-expr (term->expr t) ctx)
              (if (empty? next-progs)
                  (list)
                  (rec lang (caar next-progs) (cdar next-progs))))))
    (deduplicate (rec lang t ctx)))
  
  (define (emit t)
    (let [[t2 (unexpand-term t)]]
      (if (could-not-unexpand? t2)
          (show-skip t)
          (show-step t2))))
  
  ; macro-aware-eval* : Language expr ctx -> pattern -> void
  ; A callback-based version of macro-aware-eval.
  (define (macro-aware-eval* convert steps s [emit emit])
    (let [[t (expand-term s)]]
      (steps (convert t) emit)))
)