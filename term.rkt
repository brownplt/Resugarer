(module term racket
  (provide (all-defined-out))
  (require parser-tools/lex)
  (require ragg/support)
  (require (except-in rackunit fail))
  (require "utility.rkt")
  (require "grammar.rkt")

  #| Tag ::= MacHead(macro-name, case-number, origin-term)
             -- Marks root of macro-originating code.
           | MacBody: Marks code that originated from a macro.
           | Alien: Marks code that is not from here. |#
  (struct MacHead (m c q) #:transparent)
  (struct MacBody () #:transparent)
  (struct Alien () #:transparent)
  
  #| Term ::= Node(Label, listof(Term))
            | Tagged(listof(Tag), Term)
            | Symbol
            | Integer
            | Float |#
  (struct Node (label terms) #:transparent)
  (struct List (terms) #:transparent)
  
  (define-setting DEBUG_COMMUNICATION set-debug-communication! #f)
  
  
  #| PRINTING |#
  
  (define (show-term t)
    (define (parens x) (format "(~a)" x))
    (define (braces x) (format "{~a}" x))
    (define (brackets x) (format "[~a]" x))
    (define (comma-sep xs) (string-join xs ", "))
    (define (origins->string os)
      (braces (brackets (comma-sep (map show-origin os)))))
    (define (show-node l . ts)
      (string-append (symbol->string l) (parens (comma-sep ts))))
    (define (show-string s) (format "~v" s))
    (define (show-symbol s) (format "~v" (symbol->string s)))
    (define (show-number n) (show-string (number->string n)))
    (define (show-origin o)
      (match o
        [(MacHead m c q)
         (string-append "Head"
            (parens (comma-sep (list (symbol->string m) (number->string c) (show-term q)))))]
        [(MacBody)
         "Body"]
        [(Alien) ; Not yet supported by Resugarer
         "Alien"]))
    (define (show-list xs)
      (brackets (comma-sep xs)))
    (define (show-binding b)
      (match b [(list v x)
                (show-node 'Binding (show-symbol v) (show-term x))]))
    (define (show-cond-case c)
      (match c [(list c x)
                (show-node 'CondCase (show-term c) (show-term x))]))
    (match t
      [(Tagged os t)
       (string-append (show-term t) (origins->string os))]
      [(? string? t)
       (show-node 'Str (show-string t))]
      [(? number? t)
       (show-node 'Num (show-number t))]
      [(? symbol? t)
       (show-node 'Id (show-string (symbol->string t)))]
      [(list 'let (list bs ...) xs ...)
       (show-node 'Let (show-list (map show-binding bs))
                       (show-list (map show-term xs)))]
      [(list 'cond (list cs ...))
       (show-node 'Cond (show-list (map show-cond-case cs)))]
      [(list 'begin x xs ...)
       (show-node 'Begin (show-list (map show-term (cons x xs))))]
      [(list 'if x y z)
       (show-node 'If (show-term x) (show-term y) (show-term z))]
      [(list 'lambda (list (? symbol? vs) ...) x)
       (show-node 'Lambda (show-list (map show-symbol vs)) (show-term x))]
      [(list 'set! (? symbol? v) x)
       (show-node 'Set (symbol->string v) (show-term x))]
      [(list f xs ...)
       (show-node 'Apply (show-term f) (show-list (map show-term xs)))]
      [val
       val]))
  
  
  #| PARSING |#
  ; (also see grammar.rkt)
  
  (define (read-term str)
    (define (extract-list xs)
      (cond [(empty? xs) (list)]
            [(and (cons? xs) (string? (car xs))) (extract-list (cdr xs))]
            [(cons? xs) (cons (car xs) (extract-list (cdr xs)))]))
    (define (strip-quotes str)
      (substring str 1 (- (string-length str) 1)))
    (define (ast->term x)
      (match x
        [(? string? x)       (strip-quotes x)]
        [`(tag "Body")       (MacBody)]
        [`(tag "Alien")      (Alien)]
        [`(tag "Head" ,_ ,l ,_ ,i ,_ ,t ,_)
                             (MacHead (string->symbol l) (string->number i) (ast->term t))]
        [`(tags . ,xs)       (map ast->term (extract-list xs))]
        [`(terms . ,xs)      (map ast->term (extract-list xs))]
        [`(list ,_ ,xs ,_)   (ast->term xs)]
        [`(node ,l ,_ ,x ,_) (Node (string->symbol l) (ast->term x))]
        [`(term ,x)          (ast->term x)]
        [`(term ,x ,o)       (Tagged (ast->term o) (ast->term x))]))
    (define (convert-origin o)
      (match o
        [(MacBody) (MacBody)]
        [(MacHead m i t) (MacHead m i (convert t))]
        [(Alien) (Alien)]))
    (define (convert t)
      (match t
        [(Node 'Id (list x))
         (string->symbol x)]
        [(Node 'Str (list x))
         x]
        [(Node 'Num (list x))
         (string->number x)]
        [(Node 'Apply (list f xs))
         (map convert (cons f xs))]
        [(Node 'Lambda (list vs x))
         (list 'lambda (map string->symbol vs) (convert x))]
        [(Node 'Binding (list v b))
         (list (string->symbol v) (convert b))]
        [(Node 'Let (list bs xs))
         (cons 'let (cons (map convert bs) (map convert xs)))]
        [(Node 'Begin (list xs))
         (cons 'begin (map convert xs))]
        [(Tagged os x)
         (Tagged (map convert-origin os) (convert x))]
        [_ (fail (format "Could not parse term: ~a" t))]))
    (let [[result
    (convert (ast->term (syntax->datum (parse (tokenize (open-input-string str))))))
    ]]
      result))
  
  (define (tokenize file)
    ; Glommed together from Danny Yoo's Ragg example & pyret lang lexer
    (port-count-lines! file)
    (define lexer
      (lexer-src-pos
       ;; numbers
       [(concatenation
         (repetition 1 +inf.0 numeric)
         (union ""
                (concatenation
                 #\.
                 (repetition 1 +inf.0 numeric))))
        (token 'NUMBER lexeme)]
       ;; strings
       [(concatenation
         "\""
         (repetition 0 +inf.0 (union "\\\"" (intersection
                                             (char-complement #\")
                                             (char-complement #\newline))))
         "\"")
        (token 'STRING lexeme)] ; escaping?
       ;; tags
       [(union "Head" "Body" "Alien")
        (token lexeme lexeme)]
       ;; brackets
       [(union "[" "]" "{" "}" "(" ")" ",")
        (token lexeme lexeme)]
       ;; whitespace
       [whitespace
        (token 'WS lexeme #:skip? #t)]
       ;; labels
       [(repetition 1 +inf.0 alphabetic)
        (token 'LABEL lexeme)]
       [(eof) (void)]))
    (lambda () (lexer file)))
  
  (define (test-conversion x)
    (check-equal? x (read-term (show-term x))))

  (test-conversion (Tagged (list (MacBody) (MacBody))
                           (list '+ 'foo "bar" 3)))
  (test-conversion (Tagged (list (Alien))
                           `(+ (- x) 3)))
  (test-conversion (Tagged (list (MacHead 'Macro 2 `(+ x 1)))
                           `(+ x y)))
  (test-conversion `(lambda (x y) (+ x y)))
  (test-conversion `(let [] 3))
  (test-conversion `(let [[x 1] [y 2]] (+ x y)))

  
  #| RESUGARING |#
  
  (define expand-term (make-parameter #f))
  (define unexpand-term (make-parameter #f))
  
  (define (send-command cmd out)
    (when DEBUG_COMMUNICATION (display cmd))
    (display cmd out)
    (flush-output out))
  
  (define (receive-response in err)
    (let [[response (read-line in)]]
      (when DEBUG_COMMUNICATION (display response) (newline))
      (cond [(eof-object? response)
             (read-line err) (display (read-line err)) (newline)
             (fail "Received EOF")]
            [(strip-prefix "success: " response)
             => (λ (t) (read-term t))]
            [(strip-prefix "failure: " response)
             => (λ (_) (CouldNotUnexpand))]
            [(strip-prefix "error: " response)
             => (λ (msg) (fail msg))])))
)