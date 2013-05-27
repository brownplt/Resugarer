(module resugar racket
  (require rackunit)
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  (provide
   define-macro
   make-pattern
   language language-name language-pattern->term language-term->pattern language-step language-show-term
   macro-aware-step
   macro-aware-eval)
  
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
       show-term :: term -> string      ; for debugging
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
    (sexpr->pattern 't (all-macro-literals) (all-macro-names) (list)))
  
  ; macro-aware-step :: Language t c -> pattern -> c -> list (cons pattern c)
  (define (macro-aware-step lang p ctx [debug #f])
    (let [[term->pattern (language-term->pattern lang)]
          [pattern->term (language-pattern->term lang)]
          [show-term (language-show-term lang)]
          [step (language-step lang)]]
      
      (when debug
        (display (show-pattern p)) (display "\n"))
      
      (define (show-skip t)
        (display (format "SKIP ~a\n" (show-term t #t))))
      
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
              (begin (when debug (show-skip t))
                     (new-step t ctx)))))
      
      (new-step (pattern->term (expand p)) ctx)))
  
;  (define (macro-aware-step lang red p [debug #f])
;    (when debug
;      (display (show-pattern p)) (display "\n"))
;    (define (catmap f xs) (append* (map f xs)))
;    (define (step t) (apply-reduction-relation red t))
;    (define (new-step t) (catmap resugar (step t)))
;    (define (resugar t)
;      (let ((p (unexpand (term->pattern t))))
;        (if p (list p) (begin (when debug
;                                (display (format "SKIP ~a\n" (show-term t))))
;                              (new-step t)))))
;    (new-step (pattern->term (expand p))))
  
  (define (macro-aware-eval lang p ctx [debug #f])
    (let [[next-progs (macro-aware-step lang p ctx debug)]]
      (cons (show-pattern p #t)
            (if (empty? next-progs)
                (list)
                (macro-aware-eval lang (caar next-progs) (cdar next-progs) debug)))))
  
;  (define (macro-aware-eval lang red p ctx [debug #f])
;    (let ((next-patts (macro-aware-step lang red p ctx debug)))
;      (cons (show-pattern p #t)
;            (if (empty? next-patts)
;                (list)
;                (macro-aware-eval lang red (car next-patts) debug)))))

)