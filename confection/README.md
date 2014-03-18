# Confection #

Usage: Resugarer grammar-file

Begins an interactive session.

Commands:

* `desugar *term*`
* `resugar *term*`

Responses:

* `success: *term*`
* `failure: *message*`
* `error: *message*`

* Failure indicates that a resugaring failed for benign reasons.
* Error indicates that something went wrong,
  probably because of a malformed input term.
* Messages are free-form strings for human reading.


`term`s have the following grammar (a subset of Stratego ATerm grammar):

    term ::= <int> | <string> | <float>
           | <label>(term, ..., term)
           | [term, ..., term]

Each grammar file specifies a core and surface grammar, and a set of
rewrite rules. See racket/racket.grammar for an example.
