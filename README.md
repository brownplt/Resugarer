Resugarer
=========

Lifting Reduction Semantics through Syntactic Sugar


### Requirements for Language Integration ###

* AST -> Pattern
* Pattern -> AST
* Either (slow)  step::AST->AST, or
         (fast?) run::AST->(AST->void)->void