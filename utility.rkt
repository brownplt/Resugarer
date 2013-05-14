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
  
  ; show : any -> string
  (define (show x) (format "~a" x))
  
  ; shows : list<any> -> string
  (define (shows xs) (string-join (map show xs) " "))
  
  ; debug : format-str format-arg ... -> void
  (define-syntax-rule (debug str arg ...)
    (display (format str arg ...)))
)