#lang racket

(require (for-syntax syntax/parse))
(require "private/core.rkt")

(module+ test
  (require rackunit))

#|
<racket-def> := ... | (define-schema <schema-id> <schema>)        interface macro
<racket-expr> := ... | (validate-json <schema-id> <racket-expr>)  interface macro
<schema-id> := <identifier>
<schema> := string | number | boolean | null                      atomic types
          | <schema-id>                                           schema reference
          | (list-of <schema>)                                    list-of schema
          | (object <field> ...)                                  object schema
          | (? <expr>)                                            predicate schema
          | (and <schema> <schema>)                               and schema
          | (list <schema> ...)                                   list schema
<field> := (<identifier> <schema>)                                object field
|#


