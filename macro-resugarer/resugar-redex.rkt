(module resugar-redex racket
  (require redex)
  (require "resugar.rkt")
  (provide
   make-redex-language
   expand-term show-term
   define-macro macro-aware-redex-step macro-aware-traces
   macro-aware-eval ;TODO
   term->redex make-term
   ;term->pattern pattern->term ;For testing !!!
   set-debug-store! set-debug-tags! set-debug-steps!
   )
  
  (define DEBUG_STORE #f)
  (define (set-debug-store! x) (set! DEBUG_STORE x))

  ; Assume that Redex terms all have the form
  ; | (label origins x ...)
  ; | atom 
  ; where 'label' identifies the term type, e.g. λ, if, apply,
  ; 'origins' is a list of pattern origins,
  ; and 'x ...' are either subterms, having the same form.

  #|
     redex-language ctx <: language redex-term ctx:
       name :: string
       lang :: Redex language (given by define-language)
       red :: Redex reduction relation
       join :: redex-term -> ctx -> redex-term
                 e.g. expr -> store -> prog
                 e.g. x -> unit -> x
       split :: redex-term -> (cons redex-term ctx)
                  e.g. prog -> (cons expr store)
                  e.g. x -> (cons x unit)
       lookup-var :: symbol -> ctx -> (cons symbol redex-term)
  |#
  (struct redex-language language
    (red join split))
  
  (define (atomic? x)
    (or (symbol? x)
        (string? x)
        (boolean? x)
        (number? x)))
  
  (define (term->redex t)
    (match t
      [(term-list os (cons l ts))
       (cons l (cons (list 'origins os) (map term->redex ts)))]
      [(? atomic? t)
       t]))
  
  (define (make-redex-language name lang red join split lookup-var)
    
    (define (redex->term t ctx [replace-vars #f] [recurse #f])
      (define (rec t)
        (redex->term t ctx replace-vars recurse))
      (match t
        [(? symbol? t)
         (if replace-vars
             (let* [[x (lookup-var t ctx)]]
               (if x (if recurse
                         (let* [[var (car x)]
                                [val (redex->term (cdr x) ctx #f #f)]
                                [y (unexpand-term val)]]
                           (if (could-not-unexpand? y) (car x) y))
                         (car x))
                   t))
             t)]
        [(? atomic? t)
         t]
        [(cons l (cons (list 'origins os) ts))
         (term-list os (cons l (map rec ts)))]))
    
    (redex-language name
                    term->redex
                    redex->term
                    (λ (t ctx) (map split (apply-reduction-relation red (join t ctx))))
                    "Redex langs currently do not implement language-eval"
                    (λ (t ctx [replace-vars #t] [recurse #t]) (show-term (redex->term t ctx replace-vars recurse)))
                    red
                    join
                    split))
  
  (define (macro-aware-redex-step l t n)
    (let [[split (redex-language-split l)]
          [join (redex-language-join l)]
          [term->expr (language-term->expr l)]
          [expr->term (language-expr->term l)]
          [show-expr (language-show-expr l)]]

    (let [[ps (macro-aware-step
               l
               (expr->term (car (split t)) (cdr (split t)))
               (cdr (split t)))]]
      (if (< (length ps) n) #f
          (join (term->expr (expand-term (car (list-ref ps (- n 1)))))
                (cdr (list-ref ps (- n 1))))))))

  (define-struct hidden ())
  
  (define (format-term-for-traces l t)
    (let [[expr->term (language-expr->term l)]
          [split (redex-language-split l)]]
      (if (not t) "END"
          (let [[u (unexpand-term (expr->term (car (split t)) (cdr (split t)) #t))]]
            (if (could-not-unexpand? u) (hidden) (term->sexpr u))))))

  (define-syntax-rule
    (macro-aware-traces l red t rest ...)
    (traces red t
            #:pp (lambda (s a b c)
                   (default-pretty-printer
                     (format-term-for-traces l s)
                     a b c))
            #:filter (lambda (x y) x)
            rest ...))

)