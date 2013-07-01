(module pattern-untyped racket
  (provide
   sexpr->pattern pattern->sexpr make-pattern
   term->pattern pattern->term make-term show-term term->sexpr
   unify minus substitute disjoint?
   attempt-unification unification-failure?
   nominal? strip-tags strip-term-tags
   (struct-out term-list) (struct-out term-id)
   (struct-out pvar) (struct-out literal) (struct-out constant)
     (struct-out plist) (struct-out ellipsis)
   (struct-out inter-list) (struct-out inter-ellipsis)
   (struct-out CantUnify) (struct-out CantMatch) (struct-out OccursCheck)
   (struct-out t-macro) (struct-out t-syntax) (struct-out t-apply)
   (struct-out o-macro) (struct-out o-branch) (struct-out tag)
   ; testing:
   show-pattern
   inter-list-envs free-vars replace bind empty-env singleton-env)
  (require "utility.rkt")
  (require racket/string)
  (require racket/set)
  
  ; Pattern : pvar
  ;         | literal    ; e.g. $else
  ;         | constant   ; number or boolean or string
  ;         | plist (P1 ... Pn)
  ;         | ellipsis (P1 ... Pn Q* R1 ... Rm)
  ;         | tag P Orig
  ;
  ; invariant: every Q* has at least one variable.

  (struct pvar (name) #:transparent)     ; e.g. x
  (struct literal (name) #:transparent)  ; e.g. else
  (struct constant (name) #:transparent) ; e.g. lambda
  (struct plist (type elems) #:transparent)
  (struct ellipsis (type head rep tail) #:transparent)
  (struct tag (term origin) #:transparent)
  
  ; Pattern "Types" - distinguish between
  ;  * macro calls (or 2 3),
  ;  * macro syntax (else 2),
  ;  * function calls (+ 2 3)
  
  (struct t-macro (name) #:transparent)
  (struct t-syntax () #:transparent)
  (struct t-apply () #:transparent)
  (struct t-value () #:transparent)  ; currently represented as t-apply
  
  ; Origin : o-user
  ;        | o-eval
  ;        | o-macro macro-name expansion-nonce macro-case
  
  (struct o-macro (m c) #:transparent)
  (struct o-branch () #:transparent)
  
  ; Inter : Pattern
  ;       | inter-list (I1 ... In)
  ;       | inter-ellipsis (I1 ... In J* K1 ... Km)
  
  (struct inter-list (type elems) #:transparent)
  (struct inter-ellipsis (type head rep tail) #:transparent)
  
  (define (scalar? x)
    (and (not (inter-list? x))
         (not (inter-ellipsis? x))))
  
  ; 'Nominal' terms aren't terms proper and can't have origins.
  (define (nominal? p)
    (match p
      [(plist (t-syntax) _)         #t]
      [(plist (t-macro _) _)        #f]
      [(plist (t-value) _)          #t]
      [(ellipsis (t-syntax) _ _ _)  #t]
      [(ellipsis (t-macro _) _ _ _) #f]
      [(ellipsis (t-value) _ _ _)   #t]
      [(constant _)                 #t] ; TODO: tag constants!
      [_                            #f]))

  
  ;;;;;;;;;;;;
  ;; Syntax ;;
  ;;;;;;;;;;;;

  #|  Syntax Guide:
      * Literals (e.g. else) are prefixed with '$'.
      * Macros start with a capital letter.
      * Variables and Constants start with lowercase letters,
          and are distinguished by context.
      * "syntax parens" (e.g. (let ((x 1)) x)) are marked with '^'
      * '!' means "Feel free to display the following subexpression to the user.
  |#
  
  (define standard-lambda 'lambda) ; choose between λ and lambda internally
  (define printed-lambda 'λ)       ; choose between λ and lambda for printing
  
  ; Compile a racket-like macro pattern into a Pattern.
  ; Guarantees that no ellipses pattern is variableless.
  ; TODO: Verify that variables are unique
  ; Treat an id as a var if it is in vars or if vars=#f, and as a const otherwise.
  (define (sexpr->pattern p [vars #f] [opaque #f])
    (define (rec p) (sexpr->pattern p vars opaque))
    (define (make-ellipsis t l m r)
      (let [[l (map rec l)]
            [m (rec m)]
            [r (map rec r)]]
        (if (set-empty? (free-vars m))
          (fail "An ellipsis must contain variables: ~a" m)
          (ellipsis t l m r))))
    (define (macro-call? s)
      (if (or (not (cons? s)) (not (symbol? (car s))))
          #f
          (let [(str (symbol->string (car s)))]
            (and (> (string-length str) 0)
                 (char-upper-case? (string-ref str 0))))))
    (define (literal-like? sym)
      (symbol-begins-with? sym (lambda (c) (char=? c #\$))))
    (define (var-like? sym)
      (and (symbol-lower-case? sym) (or (not vars) (member sym vars))))
    (define (a-lambda? sym)
      (or (eq? sym 'λ) (eq? sym 'lambda)))
    (define (const-like? sym)
      (or (and (symbol-lower-case? sym) (not (var-like? sym)))
          (and (symbol? sym) (not (symbol-lower-case? sym)))))
    (define (marked-with-symbol? l s)
      (and (list? l) (not (empty? l)) (symbol? (car l)) (symbol=? (car l) s)))
    (define (transparency-marked? l)
      (marked-with-symbol? l '!))
    (define (local-transparency-marked? l)
      (marked-with-symbol? l '!!))
    (define (add-tag p)
      (if (and opaque (not (nominal? p)))
          (tag p (o-branch))
          p))
    (cond [(symbol? p)
           (cond
             [(literal-like? p)   (literal p)]
             [(var-like? p)       (pvar p)]
             [(a-lambda? p)       (constant standard-lambda)] ; hack
             [(const-like? p)     (constant p)]
             [else                (fail "Not a valid literal or variable: ~a" p)])]
          [(number? p)  (constant p)]
          [(boolean? p) (constant p)]
          [(string? p)  (constant p)]
          [(transparency-marked? p) (sexpr->pattern (cdr p) vars (not opaque))]
          [(list? p)
           (add-tag (match p
             [(list '^ ps ... q '... rs ...)
              (make-ellipsis (t-syntax) ps q rs)]
             [(list '^ ps ...)
              (plist (t-syntax) (map rec ps))]
             [(? macro-call? (list m ps ... q '... rs ...))
              (make-ellipsis (t-macro m) ps q rs)]
             [(? macro-call? (list m ps ...))
              (plist (t-macro m) (map rec ps))]
             [(list ps ... q '... rs ...)
              (make-ellipsis (t-apply) ps q rs)]
             [(list ps ...)
              (plist (t-apply) (map rec ps))]))]))
  
  (define-syntax-rule (make-pattern t)
    (sexpr->pattern 't (list) #f))
  
  (define (pattern->sexpr x [keep-tags? #f])
    (define (rec x) (pattern->sexpr x keep-tags?))
    (define (type->sexprs t)
      (match t
        [(t-macro m) (list m)]
        [(t-syntax) (list '^)]
        [_ (list)]))
    (define (orig->sexpr o)
      (match o
        [(o-branch) 'o-branch]
        [(o-macro m c) (list 'o-macro m c)]))
    (match x
      [(tag x o)           (if keep-tags?
                               (list 'tag (rec x) (orig->sexpr o))
                               (rec x))]
      [(pvar v)            v]
      [(literal x)         x]
      [(constant 'lambda)  printed-lambda]
      [(constant 'λ)       printed-lambda]
      [(constant x)        x]
      [(plist t elems)     (append (type->sexprs t)
                                   (map rec elems))]
      [(ellipsis t l m r)  (append (type->sexprs t)
                                   (map rec l)
                                   (list (rec m)
                                         '...)
                                   (map rec r))]))
  
  (define (show-pattern p [keep-tags? #f])
    (let [[str (format "~v" (pattern->sexpr p keep-tags?))]]
      (if (string-prefix? "'" str)
          (substring str 1)
          str)))
  
  
  ;;;;;;;;;;;;;;;;;
  ;; Unification ;;
  ;;;;;;;;;;;;;;;;;
  
  (struct CantUnify (left right) #:transparent)
  (struct CantMatch (left right) #:transparent)
  (struct OccursCheck (var pattern) #:transparent)
  
  (define (unification-failure? x)
    (or (CantUnify? x) (OccursCheck? x) (CantMatch? x)))
  
  (define-syntax-rule (attempt-unification u)
    (with-handlers [[unification-failure? id]] u))
  
  (define (unifies xs ys)
    (match* (xs ys)
      [((list) (list))            (list)]
      [((cons x xs) (cons y ys))  (cons (unify x y) (unifies xs ys))]))
  
  ; Find a minimal pattern z such that for some substitutions s and s',
  ;   z = s x = s' y
  ; Fails on patterns like (a x ...) \/ (y a ...) that may not have a
  ;   unique unification.
  (define (unify x y)
    (let [[fail (λ () (raise (CantUnify x y)))]]
      (match* (x y)
        [((tag x _) y)                (unify x y)]
        [(x (tag y _))                (unify x y)]
        [((literal x) (literal x))    (literal x)]
        [((literal x) y)              (fail)]
        [(x (literal y))              (fail)]
        [(x (pvar y))                  x]
        [((pvar x) y)                  y]
        [((constant x) (constant x))  (constant x)]
        [((constant x) y)             (fail)]
        [(x (constant y))             (fail)]
        [((plist t xs) (plist t ys))
         (if (eq? (length xs) (length ys))
             (plist t (unifies xs ys))
             (fail))]
        [((plist t xs) (ellipsis t l m r))
         (let ((m-len (- (length xs) (length l) (length r))))
           (if (< m-len 0)
               (fail)
               (plist t (unifies xs (append l (repeat m-len m) r)))))]
        [((ellipsis t l m r) (plist xt xs)) ; symmetric to case below
         (unify (plist xt xs) (ellipsis t l m r))]
        [((ellipsis t1 l1 m1 r1) (ellipsis t2 l2 m2 r2))
         (let* ((l-len (min (length l1) (length l2)))
                (r-len (min (length r1) (length r2)))
                (left (unifies (take l1 l-len) (take l2 l-len)))
                (right (unifies (take-right r1 r-len) (take-right r2 r-len))))
           (unify-ellipses
            left right
            (ellipsis t1 (drop l1 l-len) m1 (drop-right r1 r-len))
            (ellipsis t2 (drop l2 l-len) m2 (drop-right r2 r-len))))])))
  
  ; A helper: unify ellipses whose common heads and tails have been stripped.
  (define (unify-ellipses left right x y)
    (match* (x y)
      [((ellipsis t l m r) (ellipsis t '() m2 '()))
       (match (attempt-unification (unify m m2))
         [(CantUnify _ _) ; m disjoint from m2, so |m| = 0
          (let* ((x-lst (append l r))
                 (y-lst (repeat (length x-lst) m2))
                 (center (unifies x-lst y-lst)))
            (plist t (append left center right)))]
         [m3 ; 
          (let* ((l-lst (unifies (repeat (length l) m2) l))
                 (r-lst (unifies (repeat (length r) m2) r)))
            (ellipsis t (append left l-lst) m3 (append r-lst right)))])]
      [((ellipsis t '() m2 '()) (ellipsis t l1 m1 r1))
       (unify-ellipses left right y x)] ; symmetric to case above
      ; TODO: For the case below, find the *set* of all unifications,
      ;       and only fail when the set has more than one element.
      [(_ _) (no-unique-unification x y)])) ; Have (a x*) \/ (y* b)
  
  (define (no-unique-unification x y)
    (fail "unify-ellipses: There may not be a unique unification."))
  
  (define (disjoint? x y)
    (let [[result (attempt-unification (unify x y))]]
      (unification-failure? result)))
  
  
  ;;;;;;;;;;;;;;
  ;; Matching ;;
  ;;;;;;;;;;;;;;
  
  
  (define (minus x y [origin #f]) ; o: expected origin, or #f if any
    (let [[minus (λ (x y) (minus x y origin))]]
    (define (fail) (begin
                     (debug "CantMatch:\n\t~a\n\t~a\n\n" x y)
                     (raise (CantMatch (show-pattern x) (show-pattern y)))))
    (define (succeed) empty-env)
    
    (define (minuses xs ys)
      (apply hash-union (map minus xs ys)))
  
    (define (list-minuses t xs y)
      (inter-list-envs t (free-vars y) (map minus xs (repeat (length xs) y))))
  
    (define (ellipsis-minuses t l m r y)
      (inter-ellipsis-envs t
                           (free-vars y)
                           (map minus l (repeat (length l) y))
                           (minus m y)
                           (map minus r (repeat (length r) y))))
      
      (match* (x y)
        [((literal x) (literal x))     (succeed)]
        [((literal _) _)               (fail)]
        [(_ (literal _))               (fail)]
        [(x (pvar y))                  (singleton-env y x)]
        [((pvar _) _)                  (fail)]
        [((constant x) (constant x))   (succeed)]
        [((constant _) _)              (fail)]
        [(_ (constant _))              (fail)]
        [((plist t xs) (plist t ys))   (if (eq? (length xs) (length ys))
                                           (minuses xs ys)
                                           (fail))]
        [((ellipsis _ _ _ _) (plist _ _))  (fail)]
        [((plist t xs) (ellipsis t l m r))
         (let ((m-len (- (length xs) (length l) (length r))))
           (if (< m-len 0)
               (fail)
               (let ((xs:l (take xs (length l)))
                     (xs:r (take-right xs (length r)))
                     (xs:m (take (drop xs (length l)) m-len)))
                 (hash-union
                  (minuses xs:l l)
                  (list-minuses t xs:m m)
                  (minuses xs:r r)))))]
        [((ellipsis t l1 m1 r1) (ellipsis t l2 m2 r2))
         (let* ((l2-len (length l2))
                (l1-len (- (length l1) l2-len))
                (r2-len (length r2))
                (r1-len (- (length r1) r2-len)))
           (if (or (< l1-len 0) (< r1-len 0))
               (fail)
               (let [[l1:l (take l1 l2-len)]
                     [l1:r (drop l1 l2-len)]
                     [r1:l (take r1 r1-len)]
                     [r1:r (drop r1 r1-len)]]
                 (hash-union
                  (minuses l1:l l2)
                  (ellipsis-minuses t l1:r m1 r1:l m2)
                  (minuses r1:r r2)))))]
        [((tag x (o-branch)) (tag y (o-branch)))
         (minus x y)]
        [((tag x (o-macro m n)) (tag y (o-macro m n)))
         (minus x y)]
        [(_ _) (fail)])))
  
  
  ;;;;;;;;;;;;;;;;;;
  ;; Substitution ;;
  ;;;;;;;;;;;;;;;;;;
  
  ; Lemma: substitution preserved well-formedness.
  ;        (That is, it leaves no ellipsis variableless)
  
  ; assume that all vars are bound in env
  ; assume that vars are at least as deep as their bindings in env
  (define (substitute e x)
    (let [[subs (λ (x) (substitute e x))]]
      (match x
        [(tag t os)       (tag (subs t) os)]
        [(pvar v)         (hash-ref e v)]
        [(constant x)     (constant x)]
        [(literal x)      (literal x)]
        [(plist t xs)     (plist t (map subs xs))]
        [(ellipsis t l m r) (let [[head (map subs l)]
                                  [middle (substitute-rep t e m)]
                                  [tail (map subs r)]]
                            (match middle
                              [(ellipsis t l m r)
                               (ellipsis t (append head l) m (append r tail))]
                              [(plist t xs)
                               (plist t (append head xs tail))]))])))
  
  (define (substitute-rep t e x)
    
    ; slice : Extract a slice from the bindings using 'f',
    ;         add them to the environment 'e',
    ;         and substitute into 'x'
    (define (slice bindings f)
      (define (slice-binding b)
        (cons (car b) (f (cdr b))))
      (substitute (hash-add-bindings e (map slice-binding bindings)) x))
    
    (define (slices bindings f len)
      (map (λ (n) (slice bindings (λ (x) (list-ref (f x) n)))) (range len)))
    
    ; substitute-list : Given list bindings (v -> [P1..Pn]) for the rep,
    ;                   build the pattern (x1..xn), where xi is
    ;                   e substituted into x, but with each v instead bound to Pi.
    (define (substitute-list t len bindings)
      (plist t (slices bindings inter-list-elems len)))
    
    ; substitute-ellipsis : Analogous to substitute-list, but with bindings
    ;                       v -> [P1..Pn Q* R1..Rm]
    (define (substitute-ellipsis t head-len tail-len bindings)
      (ellipsis t (slices bindings inter-ellipsis-head head-len)
                  (slice bindings inter-ellipsis-rep)
                  (slices bindings inter-ellipsis-tail tail-len)))
    
    (let* ((bindings (map (λ (v) (cons v (hash-ref e v))) (set->list (free-vars x))))
           (list-bindings     (filter (λ (b) (inter-list?     (cdr b))) bindings))
           (ellipsis-bindings (filter (λ (b) (inter-ellipsis? (cdr b))) bindings))
           (scalar-bindings   (filter (λ (b) (scalar?         (cdr b))) bindings)))
      (cond [(empty? bindings)
             (fail "Substitute: ellipsis without variables")]
            [(and (empty? list-bindings) (empty? ellipsis-bindings))
             (fail "Substitute: ellipsis with mismatched variable bindings")]
            [(and (not (empty? list-bindings)) (not (empty? ellipsis-bindings)))
             (fail "Substitute: ellipsis does not contain variables of sufficient depths")]
            [(empty? ellipsis-bindings)
             (let ((list-lens (map (λ (b) (length (inter-list-elems (cdr b)))) list-bindings)))
               (if (not (all-eq? list-lens))
                   (fail "Substitute: ellipsis variables of differing lengths")
                   (substitute-list t (car list-lens) list-bindings)))]
            [(empty? list-bindings)
             (let ((head-lens (map (λ (b) (length (inter-ellipsis-head (cdr b))))
                                   ellipsis-bindings))
                   (tail-lens (map (λ (b) (length (inter-ellipsis-tail (cdr b))))
                                   ellipsis-bindings)))
               (if (or (not (all-eq? head-lens)) (not (all-eq? tail-lens)))
                   (fail "Substitute: ellipsis variables of differing lengths'")
                   (substitute-ellipsis t (car head-lens)
                                          (car tail-lens)
                                          ellipsis-bindings)))])))
  
  
  ;;;;;;;;;;;
  ;; Terms ;;
  ;;;;;;;;;;;
  
  ; A helpful intermediate format for closed patterns.
  
  ; term ::= term-list listof(tag) listof(term)
  ;        | term-id term
  ;        | symbol | number | ...
  (struct term-list (tags terms) #:transparent)
  (struct term-id (tags term) #:transparent) ; The identity function; useful only for its tags
  
  (define (strip-term-tags t)
    (match t
      [(term-id tags term)
       (strip-term-tags term)]
      [(term-list tags terms)
       (term-list (list) (map strip-term-tags terms))]
      [x x]))
  
  (define (pattern->term p)
    (match p
      [(constant c)           c]
      [(literal l)            l]
      [(plist (t-apply) ps)   (term-list (list) (map pattern->term ps))]
      [(plist (t-syntax) ps)  (term-list (list) (cons '^ (map pattern->term ps)))]
      [(plist (t-macro m) ps) (term-list (list) (cons m (map pattern->term ps)))]
      [(tag p o)              (match (pattern->term p)
                                [(term-list os ps) (term-list (cons o os) ps)]
                                [(term-id os p) (term-id (cons o os) p)]
                                [x (term-id (list o) x)])]))
  
  (define (term->pattern t)
    (match t
      [(term-list (list) (cons (? symbol-upper-case? t) ts))
       (plist (t-macro t) (map term->pattern ts))]
      [(term-list (list) (cons '^ ts))      (plist (t-syntax) (map term->pattern ts))]
      [(term-list (list) ts)                (plist (t-apply) (map term->pattern ts))]
      [(term-list (cons o os) ts)           (tag (term->pattern (term-list os ts)) o)]
      [(term-id (list) t)                   (term->pattern t)]
      [(term-id (cons o os) t)              (tag (term->pattern (term-id os t)) o)]
      [(? (λ (x) (symbol-prefix? "$" x)) l) (literal l)]
      [(or 'λ 'lambda)                      (constant standard-lambda)] ; hack
      [x                                    (constant x)]))
  
  (define-syntax-rule (make-term t)
    (pattern->term (make-pattern t)))
  
  (define (show-term t)
    (show-pattern (term->pattern t)))
  
  (define (term->sexpr t)
    (pattern->sexpr (term->pattern t)))
  
  
  ;;;;;;;;;;;;;;;;;;
  ;; Environments ;;
  ;;;;;;;;;;;;;;;;;;
  
  ; Env : HashMap<Symbol, Inter>
  
  (define empty-env (make-immutable-hash '()))
  
  (define (singleton-env v x) (make-immutable-hash (list (cons v x))))

  ; inter-envs : Set(Var) List(Env) -> Env
  ; (list {x -> x1, y -> y1 ...} ... {x -> xn, y -> yn ...})
  ; -> {x -> (inter x1 ... xn), y -> (inter y1 ... yn)}
  (define (inter-list-envs t vars envs)
    (make-immutable-hash
     (map (λ (v) (cons v (inter-list t (map (λ (e) (hash-ref e v)) envs))))
          (set->list vars))))
  
  (define (inter-ellipsis-envs t vars l-envs m-env r-envs)
    (make-immutable-hash
     (map (λ (v) (cons v (inter-ellipsis t
                                         (map (λ (e) (hash-ref e v)) l-envs)
                                         (hash-ref m-env v)
                                         (map (λ (e) (hash-ref e v)) r-envs))))
          (set->list vars))))
  
  ; free-vars : Pattern -> Set<Symbol>
  (define (free-vars x)
    (match x
      [(tag t _) (free-vars t)]
      [(pvar v) (set v)]
      [(literal _) (set)]
      [(constant _) (set)]
      [(plist t l) (set-unions (map free-vars l))]
      [(ellipsis t l m r)
       (set-union (set-unions (map free-vars l))
                  (free-vars m)
                  (set-unions (map free-vars r)))]))
  
  ; strip-tags : Pattern -> Pattern
  (define (strip-tags x)
    (if (tag? x) (strip-tags (tag-term x)) x))
  
  ; occurs? : Var Pattern -> Bool
  (define (occurs? v x) (set-member? (free-vars x) v))
  
  ; replace : Env Pattern -> Pattern
  (define (replace s x)
    (define (replaces s lst) (map (λ (x) (replace s x)) lst))
    (match x
      [(tag t os) (tag (replace s t) os)]
      [(pvar v) (if (hash-has-key? s v) (hash-ref s v) x)]
      [(literal _) x]
      [(constant _) x]
      [(plist t lst) (plist t (replaces s lst))]
      [(ellipsis t l m r) (ellipsis t (replaces s l) (replace s m) (replaces s r))]))
  
  ; replace-one : Var Pattern Pattern -> Pattern
  (define (replace-one v x y)
    (replace (singleton-env v x) y))
  
  ; bind : Symbol Pattern Env -> Env
  (define (bind v x e)
    (let ((x (replace e x)))
      (if (occurs? v x)
          (raise (OccursCheck v x))
          (let ((e (hash-modify e (λ (y) (replace-one v x y)))))
            (if (hash-has-key? e v)
                (fail "Variable ~a bound twice!" v)
                (hash-set e v x))))))

)