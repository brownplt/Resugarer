(module resugar racket
  (require (except-in rackunit fail))
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  (provide
   define-macro
   make-pattern test-expand
   language language-name language-pattern->term language-term->pattern language-step language-show-term
   macro-aware-step
   macro-aware-eval
   macro-aware-eval*
   set-debug-tags! set-debug-steps!)
  
  (define DEBUG_TAGS #f)
  (define (set-debug-tags! x) (set! DEBUG_TAGS x))
  (define DEBUG_STEPS #f)
  (define (set-debug-steps! x) (set! DEBUG_STEPS x))
  
  #|
     A language is free to work over whatever sort of terms and contexts it wants.
     It must take evaluation steps over (term, context) pairs.
     Contexts are hidden and do not get unexpanded.
     pattern->term and term->pattern *must* be inverses of each other,
       or else the semantic properties of the stepper are lost.

     Language term ctx {
       name :: string
       pattern->term :: pattern -> term
       term->pattern :: term -> pattern
       step :: term -> ctx -> list (cons term ctx)
       show-term :: term -> ctx -> string      ; for debugging
     }
 
                                 init-ctx
                                    ↓
     pattern  ===>  term  --->  (term, ctx)
                                    ↓
     pattern  <===  term  <---  (term, ctx)
                                    ↓
                                   ...
     (===> expansion/unexpansion)
     (---> just pairing/unpairing)
     (↓    evaluation step)
  |#
  
  (struct language
    (name pattern->term term->pattern step show-term))
  
  (define-syntax-rule (make-pattern t)
    (sexpr->pattern 't (list) #f))
  
  (define-syntax-rule (test-expand p)
    (expand (make-pattern p)))
  
  ; macro-aware-step :: Language t c -> pattern -> c -> list (cons pattern c)
  (define (macro-aware-step lang p ctx)
    (let [[term->pattern (language-term->pattern lang)]
          [pattern->term (language-pattern->term lang)]
          [show-term (language-show-term lang)]
          [step (language-step lang)]]
      
      (when DEBUG_STEPS
        (display (show-term (pattern->term p) ctx)) (display "\n\n"))
        ;(display (show-pattern p)) (display "\n"))
      
      (define (show-skip t ctx)
        (display (format "SKIP ~a\n\n" (show-term t ctx DEBUG_TAGS))))
      
      (define (catmap f xs)
        (append* (map f xs)))
      
      (define (new-step t ctx)
        (catmap resugar (step t ctx)))
      
      (define (resugar prog)
        (let* [[t (car prog)]
               [ctx (cdr prog)]
               [p (unexpand (term->pattern t))]]
          (if p
              (list (cons p ctx))
              (begin (when DEBUG_STEPS (show-skip t ctx))
                     (new-step t ctx)))))
      
      (new-step (pattern->term (expand p)) ctx)))
  
  ; macro-aware-eval :: Language t c -> pattern -> c -> list (cons pattern c)
  (define (macro-aware-eval lang p ctx)
    (define (rec lang p ctx)
      (let [[next-progs (macro-aware-step lang p ctx)]
            [show-term (language-show-term lang)]
            [pattern->term (language-pattern->term lang)]]
        (cons (show-term (pattern->term p) ctx)
              (if (empty? next-progs)
                  (list)
                  (rec lang (caar next-progs) (cdar next-progs))))))
    (deduplicate (rec lang p ctx)))
  
  ; macro-aware-eval* : (pattern -> term)
  ;                  -> (term -> (pattern -> void) -> void)
  ;                  -> void
  ; A callback-based version of macro-aware-eval.
  (define (macro-aware-eval* pattern->term steps p)
    
    (define last #f)
    
    (define (output-line str)
      (when (not (equal? str last))
        (display str) (newline)
        (set! last str)))
    
    (define (show-step p)
      (output-line (show-pattern p)))
    
    (define (show-skip p)
      (when DEBUG_STEPS
        (output-line (format "SKIP: ~a" (show-pattern p)))))
    
    (define (callback p)
      (let [[p* (unexpand p)]]
        (if p* (show-step p*) (show-skip p))))
    
    (steps (pattern->term (expand p)) callback))

)