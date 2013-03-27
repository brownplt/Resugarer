(module pattern-untyped racket
  (provide
   sexpr->pattern
   unify minus substitute
   attempt-unification unification-failure?
   add-global-literals! is-macro-literal? all-macro-literals
   (struct-out pvar) (struct-out literal) (struct-out constant)
     (struct-out plist) (struct-out ellipsis)
   (struct-out inter-list) (struct-out inter-ellipsis)
   (struct-out CantUnify) (struct-out CantMatch) (struct-out OccursCheck)
   (struct-out t-macro) (struct-out t-syntax) (struct-out t-apply)
   (struct-out o-user) (struct-out o-macro) (struct-out o-eval)
   ; testing:
   show-pattern
   inter-list-envs free-vars replace bind empty-env singleton-env)
  
  (require "utility.rkt")
  (require racket/string)
  (require racket/set)
  
  ; Pattern : pvar
  ;         | literal
  ;         | constant   ; symbol or number
  ;         | plist (P1 ... Pn)
  ;         | ellipsis (P1 ... Pn Q* R1 ... Rm)
  ;
  ; invariant: every Q* has at least one variable.

  (struct pvar (name) #:transparent)     ; e.g. x
  (struct literal (name) #:transparent)  ; e.g. else
  (struct constant (name) #:transparent) ; e.g. lambda
  (struct plist (type elems) #:transparent)
  (struct ellipsis (type head rep tail) #:transparent)
  
  ; Pattern "Types" - distinguish between
  ;  * macro calls (or 2 3),
  ;  * macro syntax (else 2),
  ;  * function calls (+ 2 3)
  
  (struct t-macro (name origin) #:transparent)
  (struct t-syntax () #:transparent)
  (struct t-apply (origin) #:transparent)
  
  ; Origin : o-user
  ;        | o-eval
  ;        | o-macro macro-name expansion-nonce macro-case
  
  (struct o-user () #:transparent)
  (struct o-macro (m i c) #:transparent)
  (struct o-eval () #:transparent)
  
  ; Inter : Pattern
  ;       | inter-list (I1 ... In)
  ;       | inter-ellipsis (I1 ... In J* K1 ... Km)
  
  (struct inter-list (type elems) #:transparent)
  (struct inter-ellipsis (type head rep tail) #:transparent)
  
  (define (scalar? x)
    (and (not (inter-list? x))
         (not (inter-ellipsis? x))))
  
  (define (make-ellipsis t l m r)
    (if (set-empty? (free-vars m))
        (error (format "Empty ellipses: ~a" m))
        (ellipsis t l m r)))
  
  
  ; Keep a global list of macro keywords,
  ; just to infer which s-expr identifiers should be treated as literals.  
  (define global-macro-literal-set (set))
  
  (define (add-global-literals! lits)
    (set! global-macro-literal-set
          (foldl (λ (lit s) (set-add s lit)) global-macro-literal-set lits)))
  
  (define (is-macro-literal? x)
    (and (literal? x)
         (set-member? global-macro-literal-set (literal-name x))))
  
  (define (all-macro-literals)
    (set->list global-macro-literal-set))
  
  (define (show-pattern x [abbreviated #f])
    (define (show-type t)
      (match t
        [(t-macro m _) (format "~a " m)]
        [(t-syntax)    (if abbreviated "" "^ ")]
        [(t-apply _)   ""]
        [_             "[Not a type!]"])) ; !!!
    (let ((show-pattern (λ (x) (show-pattern x abbreviated))))
      (match x
        [(pvar v)            (symbol->string v)]
        [(literal x)         (format ":~a" (symbol->string x))]
        [(constant x)        (if abbreviated
                                 (show x)
                                 (format "'~a" (show x)))]
        [(plist (t-syntax) elems)
                             (format "[~a]"
                                     (string-join (map show-pattern elems) " "))]
        [(plist t elems)     (format "(~a~a)"
                                     (show-type t)
                                     (string-join (map show-pattern elems) " "))]
        [(ellipsis t l m r)  (format "(~a~a)"
                                     (show-type t)
                                     (string-join
                                      (append (map show-pattern l)
                                              (list (show-pattern m))
                                              (list "...")
                                              (map show-pattern r))
                                      " "))])))
  
  
  ;;;;;;;;;;;;
  ;; Syntax ;;
  ;;;;;;;;;;;;
  
  ; Compile a racket-like macro pattern into a Pattern.
  ; Guarantees that no ellipses pattern is variableless.
  ; TODO: Verify that variables are unique
  (define (sexpr->pattern p lits macs vars origin)
    (let ((sexpr->pattern (λ (p) (sexpr->pattern p lits macs vars origin))))
      (cond [(symbol? p)
             (cond
               [(member p lits)                 (literal p)]
               [(or (not vars) (member p vars)) (pvar p)]
               [else                            (constant p)])]
            [(number? p)  (constant p)]
            [(boolean? p) (constant p)]
            [(list? p)
             (match p
               [(list '^ ps ... q '... rs ...) ; (^ P1 ... Pn Q* R1 ... Rm)
                (make-ellipsis (t-syntax)
                               (map sexpr->pattern ps)
                               (sexpr->pattern q)
                               (map sexpr->pattern rs))]
               [(list '^ ps ...) ; (^ P1 ... Pn)
                (plist (t-syntax) (map sexpr->pattern ps))]
               [(list ps ... q '... rs ...) ; (P1 ... Pn Q* R1 ... Rm)
                (if (and (cons? ps) (member (car ps) macs))
                    (make-ellipsis (t-macro (car ps) origin)
                                   (map sexpr->pattern (cdr ps))
                                   (sexpr->pattern q)
                                   (map sexpr->pattern rs))
                    (make-ellipsis (t-apply origin)
                                   (map sexpr->pattern ps)
                                   (sexpr->pattern q)
                                   (map sexpr->pattern rs)))]
               [(list ps ...) ; (P1 ... Pn)
                (if (and (cons? ps) (member (car ps) macs))
                    (plist (t-macro (car ps) origin)
                           (map sexpr->pattern (cdr ps)))
                    (plist (t-apply origin)
                           (map sexpr->pattern ps)))])])))
  
  
  ;;;;;;;;;;;;;;;;;
  ;; Unification ;;
  ;;;;;;;;;;;;;;;;;
  
  (struct CantUnify (left right) #:transparent)
  (struct CantMatch (left right) #:transparent)
  (struct OccursCheck (var pattern) #:transparent)
  
  (define (unification-failure? x)
    (or (CantUnify? x) (OccursCheck? x) (CantMatch? x)))
  
  (define-syntax-rule (attempt-unification u)
    (with-handlers ((unification-failure? id)) u))
  
  (define (unifies xs ys)
    (match* (xs ys)
      [((list) (list))            (list)]
      [((cons x xs) (cons y ys))  (cons (unify x y) (unifies xs ys))]))
  
  ; Find a minimal pattern z such that for some substitutions s and s',
  ;   z = s x = s' y
  ; Fails on patterns like (a x ...) \/ (y a ...) that may not have a
  ;   unique unification.
  (define (unify x y)
    (let ((fail (λ () (raise (CantUnify x y)))))
      (match* (x y)
        [((literal x) (literal x))    (literal x)]
        [((literal x) y)              (fail)]
        [(x (literal y))              (fail)]
        [(x (pvar y))                  x]
        [((pvar x) y)                  y]
        [((constant x) (constant x))  (constant x)]
        [((constant x) y)             (fail)]
        [(x (constant y))             (fail)]
        [((plist xt xs) (plist yt ys))
         (if (eq? (length xs) (length ys))
             (plist (unify-types xt yt) (unifies xs ys))
             (fail))]
        [((plist xt xs) (ellipsis t l m r))
         (let ((m-len (- (length xs) (length l) (length r))))
           (if (< m-len 0)
               (fail)
               (plist (unify-types xt t) (unifies xs (append l (repeat m-len m) r)))))]
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
      [((ellipsis t l m r) (ellipsis t2 '() m2 '()))
       (match (attempt-unification (unify m m2))
         [(CantUnify _ _) ; m disjoint from m2, so |m| = 0
          (let* ((x-lst (append l r))
                 (y-lst (repeat (length x-lst) m2))
                 (center (unifies x-lst y-lst)))
            (plist (unify-types t t2) (append left center right)))]
         [m3 ; 
          (let* ((l-lst (unifies (repeat (length l) m2) l))
                 (r-lst (unifies (repeat (length r) m2) r)))
            (ellipsis (unify-types t t2) (append left l-lst) m3 (append r-lst right)))])]
      [((ellipsis t2 '() m2 '()) (ellipsis t1 l1 m1 r1))
       (unify-ellipses left right y x)] ; symmetric to case above
      ; TODO: For the case below, find the *set* of all unifications,
      ;       and only fail when the set has more than one element.
      [(_ _) (no-unique-unification x y)])) ; Have (a x*) \/ (y* b)
  
  (define (unify-types t1 t2)
    (match* [t1 t2]
      [[(t-syntax)     (t-syntax)]     (t-syntax)]
      [[(t-apply o1)   (t-apply o2)]   (t-apply o1)] ; !!! Need o1=o2?
      [[(t-macro m o1) (t-macro m o2)] (t-macro m o1)]
      [[_ _]                           (raise (CantUnify t1 t2))]))
  
  (define (no-unique-unification x y)
    (error "unify-ellipses: There may not be a unique unification."))
  
  
  ;;;;;;;;;;;;;;
  ;; Matching ;;
  ;;;;;;;;;;;;;;
  
  
  (define (minus x y [o #f]) ; o: expected origin, or #f if any
    (let ((minus (λ (x y) (minus x y o))))
    
    (define (type-minus t1 t2)
      (match* [t1 t2]
        [[(t-syntax)    (t-syntax)]    (t-syntax)]
        [[(t-apply o)   (t-apply _)]   (t-apply o)]
        [[(t-macro m o) (t-macro m _)] (t-macro m 0)]
        [[_ _]                         (raise (CantMatch t1 t2))]))
    
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

      
    (let ((fail (λ () (raise (CantMatch x y))))
          (succeed (λ () empty-env)))
      ;(display (format "\t\tMatch ~a - ~a\n" (show-pattern x) (show-pattern y)))
      (match* (x y)
        [((literal x) (literal x))     (succeed)]
        [((literal _) _)               (fail)]
        [(_ (literal _))               (fail)]
        [(x (pvar y))                  (singleton-env y x)]
        [((pvar _) _)                  (fail)]
        [((constant x) (constant x))   (succeed)]
        [((constant _) _)              (fail)]
        [(_ (constant _))              (fail)]
        [((plist xt xs) (plist yt ys)) (if (eq? (length xs) (length ys))
                                           (begin (type-minus xt yt)
                                                  (minuses xs ys))
                                           (fail))]
        [((ellipsis _ _ _ _) (plist _ _))  (fail)]
        [((plist xt xs) (ellipsis t l m r))
         (let ((m-len (- (length xs) (length l) (length r))))
           (if (< m-len 0)
               (fail)
               (let ((xs:l (take xs (length l)))
                     (xs:r (take-right xs (length r)))
                     (xs:m (take (drop xs (length l)) m-len)))
                 (hash-union
                  (minuses xs:l l)
                  (list-minuses (type-minus xt t) xs:m m)
                  (minuses xs:r r)))))]
        [((ellipsis t1 l1 m1 r1) (ellipsis t2 l2 m2 r2))
         (let* ((l2-len (length l2))
                (l1-len (- (length l1) l2-len))
                (r2-len (length r2))
                (r1-len (- (length r1) r2-len)))
           (if (or (< l1-len 0) (< r1-len 0))
               (fail)
               (let [[l1:l (take l1 l2-len)]
                     [l1:r (drop l1 l2-len)]
                     [r1:l (take r1 r1-len)]
                     [r1:r (drop r1 r1-len)]
                     [t    (type-minus t1 t2)]]
                 (hash-union
                  (minuses l1:l l2)
                  (ellipsis-minuses t l1:r m1 r1:l m2)
                  (minuses r1:r r2)))))]
        [(_ _) (fail)]))))
  
  
  ;;;;;;;;;;;;;;;;;;
  ;; Substitution ;;
  ;;;;;;;;;;;;;;;;;;
  
  ; Lemma: substitution preserved well-formedness.
  ;        (That is, it leaves no ellipsis variableless)
  
  ; assume that all vars are bound in env
  ; assume that vars are at least as deep as their bindings in env
  (define (substitute e x [wrap id])
    (let [[subs (λ (x) (substitute e x wrap))]]
      (match x
        [(pvar v)         (wrap (hash-ref e v))]
        [(constant x)     (constant x)] ; !!! Should leaves be wrapped?
        [(literal x)      (literal x)]
        [(plist t xs)     (wrap (plist t (map subs xs)))]
        [(ellipsis t l m r) (let [[head (map subs l)]
                                  [middle (substitute-rep t e m wrap)]
                                  [tail (map subs r)]]
                            (match middle
                              [(ellipsis t l m r)
                               (wrap (ellipsis t (append head l) m (append r tail)))]
                              [(plist t xs)
                               (wrap (plist t (append head xs tail)))]))])))
  
  (define (substitute-rep t e x wrap)
    
    ; slice : Extract a slice from the bindings using 'f',
    ;         add them to the environment 'e',
    ;         and substitute into 'x'
    (define (slice bindings f)
      (define (slice-binding b)
        (cons (car b) (f (cdr b))))
      (substitute (hash-add-bindings e (map slice-binding bindings)) x wrap))
    
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
             (error "Substitute: ellipsis without variables")]
            [(and (empty? list-bindings) (empty? ellipsis-bindings))
             (error "Substitute: ellipsis with mismatched variable bindings")]
            [(and (not (empty? list-bindings)) (not (empty? ellipsis-bindings)))
             (error "Substitute: ellipsis does not contain variables of sufficient depths")]
            [(empty? ellipsis-bindings)
             (let ((list-lens (map (λ (b) (length (inter-list-elems (cdr b)))) list-bindings)))
               (if (not (all-eq? list-lens))
                   (error "Substitute: ellipsis variables of differing lengths")
                   (substitute-list t (car list-lens) list-bindings)))]
            [(empty? list-bindings)
             (let ((head-lens (map (λ (b) (length (inter-ellipsis-head (cdr b))))
                                   ellipsis-bindings))
                   (tail-lens (map (λ (b) (length (inter-ellipsis-tail (cdr b))))
                                   ellipsis-bindings)))
               (if (or (not (all-eq? head-lens)) (not (all-eq? tail-lens)))
                   (error "Substitute: ellipsis variables of differing lengths'")
                   (substitute-ellipsis t (car head-lens)
                                          (car tail-lens)
                                          ellipsis-bindings)))])))
  
  
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
      [(pvar v) (set v)]
      [(literal _) (set)]
      [(constant _) (set)]
      [(plist t l) (set-unions (map free-vars l))]
      [(ellipsis t l m r)
       (set-union (set-unions (map free-vars l))
                  (free-vars m)
                  (set-unions (map free-vars r)))]))
  
  ; occurs? : Var Pattern -> Bool
  (define (occurs? v x) (set-member? (free-vars x) v))
  
  ; replace : Env Pattern -> Pattern
  (define (replace s x)
    (define (replaces s lst) (map (λ (x) (replace s x)) lst))
    (match x
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
                (error (format "Variable ~a bound twice!" v))
                (hash-set e v x))))))

)