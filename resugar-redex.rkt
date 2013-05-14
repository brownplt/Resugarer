(module resugar-redex racket
  (require redex)
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  (require "resugar.rkt")
  (provide
   make-redex-language define-macro-aware-language
   make-pattern expand-pattern pattern->redex-term
   define-macro macro-aware-redex-step macro-aware-traces
   macro-aware-eval ;TODO
   term->pattern pattern->term ;For testing !!!
   )

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
  
  (define (term->pattern t)
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
      [(plist (t-apply) (cons l ps))
       (cons (strip-tags l)
             (cons (list 'origins (list))
                   (map pattern->term ps)))]
      [(tag p o)
       (match (pattern->term p)
         [(cons l (cons (list 'origins os) ts))
          (cons l (cons (list 'origins (cons o os)) ts))]
         [(? atomic? t) t])]
      [else (error (format "pattern->term: cannot convert pattern:\n~a" (show-pattern p)))]))
  
  (define (show-term t)
    (match t
      [(? atomic? t)
       (show t)]
      [(cons l (cons (list 'origins o) ts))
       (format "(~a)" (string-join (cons (symbol->string l)
                                         (map show-term ts)) " "))]))

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
  |#
  (struct redex-language language
    (red join split))
  
  (define (make-redex-language name lang red join split)
    (redex-language name
                    pattern->term
                    term->pattern
                    (λ (t ctx) (map split (apply-reduction-relation red (join t ctx))))
                    (λ (t) (show-term t))
                    red
                    join
                    split))
  
  (define (macro-aware-redex-step l t)
    (let [[split (redex-language-split l)]
          [join (redex-language-join l)]
          [pattern->term (language-pattern->term l)]
          [term->pattern (language-term->pattern l)]]
    (let [[ps (macro-aware-step
               l
               (term->pattern (car (split t)))
               (cdr (split t)))]]
      (if (empty? ps) #f
          (join (pattern->term (expand (caar ps))) (cdar ps))))))

  (define-struct hidden ())
  
  (define (format-term-for-traces l t)
    (let [[term->pattern (language-term->pattern l)]
          [split (redex-language-split l)]]
      (let [[u (unexpand (term->pattern (car (split t))))]]
        (if (not u) (hidden) (pattern->sexpr u)))))
  
  (define (filter-term-for-traces l t)
    (let [[term->pattern (language-term->pattern l)]
          [split (redex-language-split l)]]
      (display (format "~a\n\n" (term->pattern (car (split t)))))
      (unexpand (term->pattern (car (split t))))))

  (define (macro-aware-traces l t)
    (traces (redex-language-red l) t ; (test-trace p)
          #:pp (lambda (t a b c)
                 (default-pretty-printer (format-term-for-traces l t)
                   a b c))
          #:filter (lambda (t _) #t)))
;                     (filter-term-for-traces l t))))
  
  (define-syntax (define-macro-aware-language stx)
    (syntax-case stx ()
      [(_ lang-name defn ...)
       (let* [[insert-origin/prod (λ (o p)
               (if (symbol? p) p (cons (car p) (cons o (cdr p)))))]
              [insert-origin/defn (λ (o d)
               (cons (car d) (map (λ (p) (insert-origin/prod o p)) (cdr d))))]
              [insert-origin (λ (o ds)
               (cons (list o (list 'origins 'any))
                     (map (λ (d) (insert-origin/defn o d)) ds)))]]
         (with-syntax [[(defn* ...)
                        (datum->syntax stx
                          (insert-origin 'o (syntax->datum #'(defn ...))))]]
           #'(define-language lang-name defn* ...)))]))
  
  #|
  (define-syntax (macro-aware-reduction-relation stx)
    (syntax-case stx ()
      (syntax-case stx ()
        [(_ lang 
  
  (define-syntax (define-macro-aware-metafunction stx)
    (syntax-case stx ()
      [(_ lang fun part ...)
       (let* [[i 0]
              [insert-origin (λ (o x))
                (if (
|#
  
  ; TODO: test cases
  
  ;(define-syntax-rule (test-conversion t)
;  (check-equal? (pattern->term (term->pattern (term t)))
;                (term t)))

;(test-conversion (+ (origins ()) 1 2))
;(test-conversion (if0 (origins (a b)) (+ (origins (b a)) x 3) 5 6))
)