(module utility racket
  (provide (all-defined-out))
  
    (define-syntax-rule (thunk x) (λ () x))
  
  (define id (λ (x) x))
  
  ; range : int -> [int]
  (define (range n)
    (if (eq? n 0) (list) (append (range (- n 1)) (list (- n 1)))))
  
  ; all-eq : [a] -> bool
  (define (all-eq? xs)
    (if (empty? xs) true
        (andmap (λ (x) (eq? x (car xs))) (cdr xs))))
  
  ; compose : a [a -> a] -> a
  (define (compose x fs)
    (if (empty? fs) x (compose ((car fs) x) (cdr fs))))
  
  ; hash-modify : (HashMap k a) (a -> a) -> (HashMap k a)
  (define (hash-modify hash func)
    (foldl (λ (key hash) (hash-update hash key func))
           hash
           (hash-keys hash)))
  
  ; hash-add-bindings : (HashMap k a) (list (pair k a)) -> (HashMap k a)
  (define (hash-add-bindings hash bindings)
    (foldl (λ (binding hash) (hash-set hash (car binding) (cdr binding)))
           hash
           bindings))
  
  ; split-list : a [a] -> (cons [a] [a]) | False
  (define (split-list delim lst)
    (let ((l (member delim (reverse lst)))
          (r (member delim lst)))
      (cond [(and (list? l) (list? r))
             (cons (reverse (cdr l)) (cdr r))]
            [else false])))
  
  ; repeat : a int -> [a]
  (define (repeat n elem)
    (if (zero? n)
        (list)
        (cons elem (repeat (- n 1) elem))))
  
  ; why can't set-union take no arguments??
  (define (set-unions sets)
    (if (empty? sets)
        (set)
        (apply set-union sets)))
  
  ; hash-union : Env ... -> Env
  ; Take the union of a list of hashmaps, assuming they are all disjoint.
  (define (hash-union . es)
    (make-immutable-hash (apply append (map hash->list es))))
  
  ; deduplicate : list -> list
  ; Remove adjacent duplicates from a list, like unix 'uniq'
  (define (deduplicate l [same? equal?])
    (match l
      [(list) (list)]
      [(list x) (list x)]
      [(cons x (cons y ys))
       (if (same? x y)
           (deduplicate (cons y ys))
           (cons x (deduplicate (cons y ys))))]))
  
  ; symbol-begins-with? : symbol -> (char -> bool) -> bool
  (define (symbol-begins-with? sym pred)
    (and (symbol? sym)
         (> (string-length (symbol->string sym)) 0)
         (pred (string-ref (symbol->string sym) 0))))
  
  ; symbol-upper-case? : symbol -> bool
  ; Does a symbol begin with an upper-case letter?
  (define (symbol-upper-case? sym)
    (symbol-begins-with? sym char-upper-case?))
  
  ; symbol-lower-case? : symbol -> bool
  ; Does a symbol begin with a lower-case letter?
  (define (symbol-lower-case? sym)
    (symbol-begins-with? sym char-lower-case?))
  
  ; string-prefix? : string -> string -> bool
  ; Does 'string' begin with 'prefix'?
  (define (string-prefix? prefix string)
    (and (>= (string-length string) (string-length prefix))
         (string=? prefix (substring string 0 (string-length prefix)))))
  
  ; show : any -> string
  (define (show x) (format "~a" x))
  
  ; shows : list<any> -> string
  (define (shows xs) (string-join (map show xs) " "))
  
  ; use-debug : bool
  (define use-debug #f)
  
  ; debug : format-str format-arg ... -> void
  (define-syntax-rule (debug str arg ...)
    (when use-debug (display (format str arg ...))))

  ; fail : format-str format-arg ... -> void
  (define-syntax-rule (fail str arg ...)
    (error (format str arg ...)))
)