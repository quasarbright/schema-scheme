#lang racket

(require syntax/parse (for-syntax syntax/stx syntax/parse))
(require (for-syntax "private/core.rkt"))
(require (for-syntax ee-lib) ee-lib/define)

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

(define-literal-forms schema-literals "schema literals cannot be used in racket expressions"
  (string number boolean null list-of list object and ?))

(begin-for-syntax
  (define-syntax-class schema
    #:literal-sets (schema-literals)
    #:description "schema"
    (pattern string)
    (pattern number)
    (pattern boolean)
    (pattern null)
    (pattern (list-of ele:schema))
    (pattern (object field:field ...))
    (pattern (? test:expr))
    (pattern (and schema1:schema schema2:schema))
    (pattern (list schema:schema ...))
    (pattern name:id))
  
  (define-syntax-class field
    #:description "object field"
    (pattern (name:id schema:schema)))

  (define/hygienic (expand-schema stx) #:expression
    (syntax-parse stx
      #:literal-sets (schema-literals)
      ; TODO this should be a special variable type, not racket-var
      [schema-name:id #:when (lookup #'schema-name racket-var?)
                      #'schema-name]
      [string #'string]
      [number #'number]
      [boolean #'boolean]
      [null #'null]
      [(list-of schema:schema)
       #'(list-of (expand-schema schema))]
      [(list schema:schema ...)
       (define/syntax-parse schemas^ (stx-map expand-schema #'(schema ...)))
       (datum->syntax #'stx (cons #'list #'schemas^) #'stx)]
      [(object (name:id schema:schema) ...)
       (define/syntax-parse fields^ (stx-map (λ (field) (list (car field) (cadr field))) #'((name schema) ...)))
       (datum->syntax #'stx (cons #'object #'fields^) #'stx)])))

(define-syntax (define-schema stx)
  (syntax-parse stx
    [(_ name:id schema:schema)
     (define/syntax-parse schema^ (expand-schema #'schema))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     #'(define (name json) (schema-compiled json))]))

(define-syntax (validate-json stx)
  (syntax-parse stx
    [(_ schema:schema json:expr)
     (define/syntax-parse schema^ (expand-schema #'schema))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     (define/syntax-parse json^ (local-expand #'json 'expression '()))
     #'(schema-compiled json^)]))



