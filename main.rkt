#lang racket
(require "private/core.rkt")
(require syntax/parse (for-syntax syntax/stx syntax/parse))
(require (for-syntax ee-lib) ee-lib/define)

(module+ test
  (require rackunit))

(provide (for-syntax expand-schema)
         define-schema
         validate-json)

#|
<racket-def> := ... | (define-schema <schema-id> <schema>)        interface macro
<racket-expr> := ... | (validate-json <schema> <racket-expr>)     interface macro
<schema-id> := <identifier>
<schema> := string | number | boolean | null                      atomic types
          | <schema-id>                                           schema reference
          | (list-of <schema>)                                    list-of schema
          | (list <schema> ...)                                   list schema
          | (object <field> ...)                                  object schema
          | (? <expr> <schema> ...)                               predicate schema
          | (and <schema> ...)                                    and schema
<field> := (<identifier> <schema>)                                object field
|#

;; EXPANDER

; define-literal-forms makes it so you can't use the literals in any racket expressions, so you can't use "list" or "and"
(begin-for-syntax
  (define-literal-set schema-literals
    #:datum-literals (string number boolean null list-of list object and ?)
    ()))

(begin-for-syntax
  (struct schema-ref [compiled-id] #:transparent)
  (define/hygienic (expand-schema stx) #:expression
    (syntax-parse stx
      #:literal-sets (schema-literals)
      [schema-name:id #:when (lookup #'schema-name schema-ref?)
                      (schema-ref-compiled-id (lookup #'schema-name schema-ref?))]
      [string #'string]
      [number #'number]
      [boolean #'boolean]
      [null #'null]
      [(list-of schema)
       (define/syntax-parse schema^ (expand-schema #'schema))
       #'(list-of schema^)]
      [(list schema ...)
       (define/syntax-parse (schema^ ...) (stx-map expand-schema #'(schema ...)))
       #'(list schema^ ...)]
      [(object (name:id schema) ...)
       ; name doesn't get expanded, it's just to avoid a conflict
       (define/syntax-parse ((name^ schema^) ...) (stx-map (λ (field) (syntax-parse field [(name:id schema) (list #'name (expand-schema #'schema))])) #'((name schema) ...)))
       #'(object (name^ schema^) ...)]
      [(and schema ...+)
       (define/syntax-parse (schema^ ...) (stx-map expand-schema #'(schema ...)))
       (foldl (λ (next and-rest) #`(and #,and-rest #,next))
              (expand-schema #'(? (const #t)))
              (syntax->list #'(schema^ ...)))]
      [(? test:expr)
       (define/syntax-parse test^ (local-expand #'test 'expression #f))
       #'(? test^)]
      [(? test:expr schema ...)
       (expand-schema #'(and (? test) schema ...))]
      [schema-name:id
       ; unbound var
       (raise-syntax-error #f "unbound schema reference" #'schema-name)])))

;; INTERFACE MACROS

(define-syntax (define-schema stx)
  (syntax-parse stx
    [(_ name:id schema)
     (define/syntax-parse schema^ (expand-schema #'schema))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     #'(begin
         (define (name-compiled json) (schema-compiled json))
         (define-syntax name (schema-ref #'name-compiled)))]))

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

(module+ test
  ; you can still use functions like "and" and "list"
  (check-equal? (and #t #f) #f)
  (check-equal? '(1 2 3) (list 1 2 3))
  (check-equal? (validate-json number 1) 1)
  (check-equal? (validate-json boolean #t) #t)
  (check-equal? (validate-json string "hello") "hello")
  (check-equal? (validate-json null 'null) 'null)
  (check-equal? (validate-json (list-of number) '(1 2 3)) '(1 2 3))
  (check-equal? (validate-json (list-of number) '()) '())
  (check-equal? (validate-json (list number boolean) '(1 #t)) '(1 #t))
  (check-equal? (validate-json (object (foo number) (bar null)) (hasheq 'bar 'null 'foo 1)) (hasheq 'bar 'null 'foo 1))
  (check-equal? (validate-json (object (foo number) (bar null)) (hasheq 'bar 'null 'foo 1 'baz 'null)) (hasheq 'bar 'null 'foo 1))
  (check-equal? (validate-json (and (list-of number) (list number number)) '(1 2)) '(1 2))
  (check-equal? (validate-json (? even?) 2) 2)
  (check-equal? (validate-json (? list? (list-of number) (list number number)) '(1 2)) '(1 2))
  (define-schema foo number)
  (check-equal? (validate-json foo 1) 1)
  (check-equal? (validate-json (list-of foo) '(1 2)) '(1 2))
  #;(define-schema rose (list-of rose))
  #;(check-equal? (validate-schema rose '(() () ((() ())))) '(() () ((() ()))))
  ; shadow built-in
  (check-equal? (local [(define-schema number boolean)] (validate-json number #t)) #t)
  (check-exn exn:fail? (thunk (validate-json number 'null)))
  (check-exn exn:fail? (thunk (validate-json boolean 'null)))
  (check-exn exn:fail? (thunk (validate-json string 'null)))
  (check-exn exn:fail? (thunk (validate-json null #t)))
  (check-exn exn:fail? (thunk (validate-json (list-of boolean) 'null)))
  (check-exn exn:fail? (thunk (validate-json (list-of boolean) (list #t 'null))))
  (check-exn exn:fail? (thunk (validate-json (list number boolean) 'null)))
  (check-exn exn:fail? (thunk (validate-json (list number boolean) '())))
  (check-exn exn:fail? (thunk (validate-json (list number boolean) '(1 #t 1))))
  (check-exn exn:fail? (thunk (validate-json (list number boolean) '(#t 1))))
  (check-exn exn:fail? (thunk (validate-json (object) 'null)))
  (check-exn exn:fail? (thunk (validate-json (object (foo number)) 'null)))
  (check-exn exn:fail? (thunk (validate-json (object (foo number)) (hasheq))))
  (check-exn exn:fail? (thunk (validate-json (object (foo number)) (hasheq 'foo #t))))
  (check-exn exn:fail? (thunk (validate-json (object (foo number)) (hasheq 'bar 1))))
  (check-exn exn:fail? (thunk (validate-json (? odd?) 2)))
  (check-exn exn:fail? (thunk (validate-json (? odd? boolean) 1))))
