(module resugar racket
  (require rackunit)
  (require redex)
  (require "utility.rkt")
  (require "pattern.rkt")
  (require "macro.rkt")
  (provide
   define-macro
   term->pattern pattern->term make-pattern
   define-macro-aware-language macro-aware-eval)
  
  (define (atomic? t) (or (symbol? t)
                          (number? t)
                          (boolean? t)))

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
        [(tag p _) (strip-tags p)]))
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
         [(? atomic? t) t])]))
  
  (define-syntax-rule (make-pattern t)
    (sexpr->pattern 't (all-macro-literals) (all-macro-names) (list)))
  
  (define (show-term t)
    (match t
      [(? atomic? t)
       (show t)]
      [(cons l (cons (list 'origins o) ts))
       (format "(~a)" (string-join (cons (symbol->string l)
                                         (map show-term ts)) " "))]))
  
  (define (expand-patt p) ; pattern -> term
    (pattern->term (expand p)))
  
  (define (unexpand-patt t) ; term -> pattern
    (unexpand (term->pattern t)))
  
  (define (macro-aware-step lang red p [debug #f])
    (when debug
      (display (show-pattern p)) (display "\n"))
    (define (catmap f xs) (append* (map f xs)))
    (define (step t) (apply-reduction-relation red t))
    (define (new-step t) (catmap resugar (step t)))
    (define (resugar t)
      (let ((p (unexpand-patt t)))
        (if p (list p) (begin (when debug
                                (display (format "SKIP ~a\n" (show-term t))))
                              (new-step t)))))
    (new-step (expand-patt p)))
  
  (define (macro-aware-eval lang red p [debug #f])
    (let ((next-patts (macro-aware-step lang red p debug)))
      (cons (show-pattern p #t)
            (if (empty? next-patts)
                (list)
                (macro-aware-eval lang red (car next-patts) debug)))))
  
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
                        ; Hope no one stumbles into this identifier.
                        (insert-origin 'mao
                           (syntax->datum #'(defn ...))))]]
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
)