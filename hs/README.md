# The Resugarer #

Usage: Resugarer grammar-file.resugar

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
  probably because of a bad input term.
* Messages are free-form strings for human reading.


`term`s have the following grammar (a subset of Stratego ATerm grammar):

    term ::= int | string | float
           | Label(term, ..., term)
           | [term, ..., term]
