#lang racket

(require (for-syntax syntax/parse))

(module+ test
  (require rackunit))

(provide (for-syntax core-schema)
         core-schema->racket)

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

; a compiled schema is a
#;(-> jsexpr? any)
; returns the result of validating, usually just the json
; or throws an error

(begin-for-syntax
  (define-syntax-class core-schema
    #:datum-literals (string number boolean null list-of object ? and list)
    #:description "core schema"
    (pattern string)
    (pattern number)
    (pattern boolean)
    (pattern null)
    (pattern (list-of ele:core-schema))
    (pattern (object field:core-field ...))
    (pattern (? test:expr))
    (pattern (and schema1:core-schema schema2:core-schema))
    (pattern (list schema:core-schema ...))
    (pattern name:id))

  (define-syntax-class core-field
    #:description "core object field"
    (pattern (name:id value:core-schema))))

(define (#%number-schema json)
  (if (number? json)
      json
      (error "expected a number" json)))

(define (#%boolean-schema json)
  (if (boolean? json)
      json
      (error "expected a boolean" json)))

(define (#%string-schema json)
  (if (string? json)
      json
      (error "expected a string" json)))

(define (#%null-schema json)
  (if (equal? 'null json)
      json
      (error "expected null" json)))

(define ((#%list-of-schema ele-schema) json)
  (if (list? json)
      (map ele-schema json)
      (error "expected a list" json)))

(define ((#%object-schema fields) json)
  (if (hash? json)
      (for/hasheq ([field fields])
        (match field
          [(list key value-schema)
           (define value (hash-ref json key (lambda () (error "expected object to have field" field json))))
           (values key (value-schema value))]))
      (error "expected an object" json)))

(define ((#%?-schema test) json)
  (if (test json)
      json
      (error "expected a value that passes a predicate" test json)))

(define ((#%and-schema schema1 schema2) json)
  (void (schema1 json))
  (schema2 json))

(define ((#%list-schema schemas) json)
  (if (and (list? json) (= (length schemas) (length json)))
      (for/list ([schema schemas] [element json])
        (schema element))
      (error (format "expected a list with ~a elements" json))))

(define-syntax (core-schema->racket stx)
  (syntax-parse stx
    ; I don't want to repeat myself, but a literal set didn't seem to work
    #:datum-literals (string number boolean null list-of object/schema ? and list)
    [(_ number) #'#%number-schema]
    [(_ boolean) #'#%boolean-schema]
    [(_ string) #'#%string-schema]
    [(_ null) #'#%null-schema]
    [(_ (list-of ele-schema:core-schema)) #'(#%list-of-schema (core-schema->racket ele-schema))]
    [(_ (object (field value-schema:core-schema) ...)) #'(#%object-schema (list (list 'field (core-schema->racket value-schema)) ...))]
    [(_ (? test:expr)) #'(#%?-schema test)]
    [(_ (and schema1:core-schema schema2:core-schema)) #'(#%and-schema (core-schema->racket schema1) (core-schema->racket schema2))]
    [(_ (list schema:core-schema ...)) #'(#%list-schema (list (core-schema->racket schema) ...))]
    [(_ name:id) #'name]))

;; interface macros for testing. these aren't the real ones

(define-syntax (define-schema stx)
  (syntax-parse stx
    [(_ name:id schema:core-schema) #'(define (name json) ((core-schema->racket schema) json))]))

(define-syntax (validate-jsexpr stx)
  (syntax-parse stx
    [(_ schema:core-schema json:expr) #'((core-schema->racket schema) json)]))

(module+ test
  (check-equal? ((core-schema->racket null) 'null) 'null)
  (check-equal? ((core-schema->racket number) 1) 1)
  (check-equal? ((core-schema->racket string) "s") "s")
  (check-equal? ((core-schema->racket boolean) #t) #t)
  (check-equal? ((core-schema->racket (list-of number)) '()) '())
  (check-equal? ((core-schema->racket (list-of number)) '(1 2 3)) '(1 2 3))
  (check-equal? ((core-schema->racket (object (foo number))) (hasheq 'foo 1)) (hasheq 'foo 1))
  (check-equal? ((core-schema->racket (? even?)) 2) 2)
  (check-equal? ((core-schema->racket (and number (? even?))) 2) 2)
  (check-equal? (validate-jsexpr (and number (? even?)) 2) 2)
  (define-schema complex (object (im number) (rl number)))
  (check-equal? (validate-jsexpr (and (? (const #t)) complex) (hasheq 'im 1 'rl 2)) (hasheq 'im 1 'rl 2))
  (define-schema rose-tree (list-of rose-tree))
  (check-equal? (validate-jsexpr rose-tree '(() () ((())))) '(() () ((()))))
  (check-equal? (validate-jsexpr (list number boolean) (list 1 #t)) (list 1 #t))
  (check-exn exn:fail? (λ () ((core-schema->racket number) #t)))
  (check-exn exn:fail? (λ () ((core-schema->racket (list-of number)) #t)))
  (check-exn exn:fail? (λ () ((core-schema->racket (list-of number)) (list 1 2 #t))))
  (check-exn exn:fail? (λ () ((core-schema->racket (? even?)) 3)))
  (check-exn exn:fail? (λ () ((core-schema->racket (and (? even?) (? (const #t)))) 1)))
  (check-exn exn:fail? (λ () ((core-schema->racket (and (? (const #t)) (? even?))) 1)))
  (check-exn exn:fail? (λ () ((core-schema->racket (and (? even?) (? even?))) 1)))
  (check-exn exn:fail? (λ () (validate-jsexpr rose-tree '(() () (((1)))))))
  (check-exn exn:fail? (λ () (validate-jsexpr (list number boolean) 1)))
  (check-exn exn:fail? (λ () (validate-jsexpr (list number boolean) '())))
  (check-exn exn:fail? (λ () (validate-jsexpr (list number boolean) '(1 2))))
  (check-exn exn:fail? (λ () (validate-jsexpr (list number boolean) '(#t #t))))
  (check-exn exn:fail? (λ () (validate-jsexpr (list number boolean) '(1 #t 3))))
  (check-exn exn:fail? (λ () (validate-jsexpr (list number boolean) '(#t 1)))))