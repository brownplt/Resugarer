(module data racket
  (provide
   (contract-out
    (struct Node ((label symbol?) (terms list?)))
    (struct List ((terms list?)))
    (struct Tagged ((tags list?) (term any/c)))
    (struct TermList ((tags list?) (terms list?)))
    (struct TermAtom ((tags list?) (term any/c))))
   (except-out (all-defined-out)
    (struct-out Node)
    (struct-out List)
    (struct-out Tagged)
    (struct-out TermList)
    (struct-out TermAtom)))
  
  (require "utility.rkt")
  (define (check-term-list? x)
    (if (list? x) #t (fail "Boom! ~a" x)))

  #| Tag ::= MacHead(macro-name, case-number, origin-term)
             -- Marks root of macro-originating code.
           | MacBody: Marks code that originated from a macro.
           | Alien: Marks code that is not from here. |#
  (struct MacHead (m c q) #:transparent)
  (struct MacBody () #:transparent)
  (struct MacTranspBody () #:transparent)
  (struct Alien () #:transparent)
  
  #| AST ::= Node(Label, listof(AST))
           | Tagged(listof(Tag), AST)
           | Symbol
           | Integer
           | Float |#
  (struct Node (label terms) #:transparent)
  (struct List (terms) #:transparent)
  (struct Tagged (tags term) #:transparent)
  (struct CouldNotUnexpand ())

  #| Term ::= TermList(listof(Tag), listof(Term))
            | TaggedTerm(listof(Tag), Term) |#
  (struct TermList (tags terms) #:transparent)
  (struct TermAtom (tags term) #:transparent)
)