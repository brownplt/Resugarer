(module resugar-redex racket
  (require redex)
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  (require "resugar.rkt")
  (provide
   make-redex-language
   make-pattern expand-pattern pattern->redex-term show-pattern
   define-macro macro-aware-redex-step macro-aware-traces
   macro-aware-eval ;TODO
   term->pattern pattern->term ;For testing !!!
   set-debug-store! set-debug-tags! set-debug-steps!
   )
  
  (define DEBUG_STORE #f)
  (define (set-debug-store! x) (set! DEBUG_STORE x))

  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)
                          (string? t)))

  ; Assume that Redex terms all have the form
  ; | (label origins x ...)
  ; | atom 
  ; where 'label' identifies the term type, e.g. λ, if, apply,
  ; 'origins' is a list of pattern origins,
  ; and 'x ...' are either subterms, having the same form.
  
  (define (term->pattern t [store #f])
    (define (origs->tags os p)
      (match os 
        [(list) p]
        [(cons o os) (tag (origs->tags os p) o)]))
    (match t
      [(? atomic? t)
       (constant t)]
      [(cons l (cons (list 'origins os) ts))
       (origs->tags os
         (plist (t-apply) (cons (constant l) (map term->pattern ts))))]))

  (define (pattern->term p)
    (define (strip-tags p)
      (match p
        [(constant l) l]
        [(tag p _) (strip-tags p)]
        [else (error (format "pattern->term: expected a constant in head-position in : ~a" (show-pattern p)))]))
    (match p
      [(constant c) c]
      [(literal l) l]
      [(plist (t-apply) (cons l ps))
       (cons (strip-tags l)
            (cons (list 'origins (list))
                  (map pattern->term ps)))]
      [(plist (t-syntax) ps)
       (map pattern->term ps)]
      [(plist (t-macro m) ps)
       (cons m (cons (list 'origins (list)) (map pattern->term ps)))]
      [(tag p o)
       (match (pattern->term p)
         [(cons l (cons (list 'origins os) ts))
          (cons l (cons (list 'origins (cons o os)) ts))]
         [(? atomic? t) t])]
      [else (error (format "pattern->term: cannot convert pattern:\n~a" (show-pattern p)))]))
  
  (define (untainted t)
    (unexpand (term->pattern t)))
  
  (define (make-show-term lookup-var)
    (define (show-origin o)
      (cond [(o-macro? o) (format "[~a:~a]" (o-macro-m o) (o-macro-c o))]
            [(o-branch? o) "!"]))
    (define (show-origins os verbose)
      (if verbose
          (string-join (map show-origin os) "")
          ""))
    (define (show-term t ctx [verbose #f] [recurse #t])
      (define (rec t)
        (match t
          [(? symbol? t)
           (let [[x (lookup-var t ctx rec)]]
             (if x
                 (if (and recurse DEBUG_STORE (untainted (cdr x)))
                     (show-term (pattern->term (unexpand (term->pattern (cdr x)))) ctx #f #f)
                     ;(format "~a:=~a" (car x) (show-term (cdr x) ctx #f #f))
                     (show (car x)))
                 (show t)))]
          [(? atomic? t)
           (format "~v" t)]
          [(cons l (cons (list 'origins o) ts))
           (format "~a(~a)"
                   (show-origins o verbose)
                   (string-join (cons (symbol->string l)
                                      (map rec ts)) " "))]
          [(? list? ts)
           (format "(^ ~a)" (string-join (map rec ts) " "))]))
      (rec t))
    show-term)

  (define expand-pattern expand)
  
  (define-syntax-rule (pattern->redex-term l p ctx)
    ((redex-language-join l) ((language-pattern->term l) p) ctx))
  

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
       lookup-var :: symbol -> ctx -> redex-term
  |#
  (struct redex-language language
    (red join split))
  
  (define (make-redex-language name lang red join split lookup-var)
    (redex-language name
                    pattern->term
                    term->pattern
                    (λ (t ctx) (map split (apply-reduction-relation red (join t ctx))))
                    (make-show-term lookup-var)
                    red
                    join
                    split))
  
  (define (macro-aware-redex-step l t)
    (let [[split (redex-language-split l)]
          [join (redex-language-join l)]
          [pattern->term (language-pattern->term l)]
          [term->pattern (language-term->pattern l)]
          [show-term (language-show-term l)]]
      (display (format "~a\n" (show-term (car (split t)) (cdr (split t)))))
    (let [[ps (macro-aware-step
               l
               (unexpand (term->pattern (car (split t))))
               (cdr (split t)))]]
      (if (empty? ps) #f
          (join (pattern->term (expand (caar ps))) (cdar ps))))))

  (define-struct hidden ())
  
  (define (format-term-for-traces l t)
    (let [[term->pattern (language-term->pattern l)]
          [split (redex-language-split l)]]
      (if (not t) "END"
          (let [[u (unexpand (term->pattern (car (split t))))]]
            (if (not u) (hidden) (pattern->sexpr u))))))

  (define-syntax-rule
    (macro-aware-traces l red t rest ...)
    (traces red t
            #:pp (lambda (s a b c)
                   (default-pretty-printer (format-term-for-traces l s)
                     a b c))
            rest ...))
  
  ; TODO: test cases
  
  ;(define-syntax-rule (test-conversion t)
;  (check-equal? (pattern->term (term->pattern (term t)))
;                (term t)))

;(test-conversion (+ (origins ()) 1 2))
;(test-conversion (if0 (origins (a b)) (+ (origins (b a)) x 3) 5 6))
)