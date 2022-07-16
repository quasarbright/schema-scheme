#lang racket
(require "private/core.rkt")
(require syntax/parse (for-syntax syntax/stx syntax/parse))
(require (for-syntax ee-lib) ee-lib/define)

(module+ test
  (require rackunit))

(provide (for-syntax expand-schema)
         define-schema
         validate-json
         string
         number
         boolean
         null
         list-of
         list
         object
         and
         ?)

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

;; EXPANDER

(define-literal-forms schema-literals "schema literals cannot be used in racket expressions"
  (string number boolean null list-of list object and ?))
; This makes it so you can't use the normal and in racket exprs

(begin-for-syntax
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
      [(list-of schema)
       #'(list-of (expand-schema schema))]
      [(list schema ...)
       (define/syntax-parse schemas^ (stx-map expand-schema #'(schema ...)))
       (datum->syntax #'stx (cons #'list #'schemas^) #'stx)]
      [(object (name:id schema) ...)
       (define/syntax-parse fields^ (stx-map (λ (field) (list (car field) (cadr field))) #'((name schema) ...)))
       (datum->syntax #'stx (cons #'object #'fields^) #'stx)])))

;; INTERFACE MACROS

(define-syntax (define-schema stx)
  (syntax-parse stx
    [(_ name:id schema)
     (define/syntax-parse schema^ (expand-schema #'schema))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     #'(define (name json) (schema-compiled json))]))

(define-syntax (validate-json stx)
  (syntax-parse stx
    [(_ schema json:expr)
     (define/syntax-parse schema^ (expand-schema #'schema))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     (define/syntax-parse json^ (local-expand #'json 'expression '()))
     #'(schema-compiled json^)]))

;; CORE

; a compiled schema is a
#;(-> jsexpr? any)
; returns the result of validating, usually just the json
; or throws an error

(define-syntax (core-schema->racket stx)
  (syntax-parse stx
    #:literal-sets (schema-literals)
    [(_ number) #'#%number-schema]
    [(_ boolean) #'#%boolean-schema]
    [(_ string) #'#%string-schema]
    [(_ null) #'#%null-schema]
    [(_ (list-of ele-schema)) #'(#%list-of-schema (core-schema->racket ele-schema))]
    [(_ (object (field value-schema) ...)) #'(#%object-schema (list (list 'field (core-schema->racket value-schema)) ...))]
    [(_ (? test:expr)) #'(#%?-schema test)]
    [(_ (and schema1 schema2)) #'(#%and-schema (core-schema->racket schema1) (core-schema->racket schema2))]
    [(_ (list schema ...)) #'(#%list-schema (list (core-schema->racket schema) ...))]
    [(_ name:id) #'name]))
