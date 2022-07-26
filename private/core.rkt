#lang racket

(provide #%number-schema
         #%boolean-schema
         #%string-schema
         #%null-schema
         #%list-of-schema
         #%list-schema
         #%object-schema
         #%?-schema
         #%and-schema
         #;(-> any/c (-> any/c any/c any) (-> any))
         #;(validate-cons json on-success on-fail)
         ; validate that `json` is a cons cell and call `on-success` with first and rest, or `(on-fail)` otherwise
         validate-cons
         #;(-> any/c any/c (-> any/c any) (-> any))
         #;(validate-object-field json key on-success on-fail)
         ; validate that `json` is an object with a field `key` and call `on-success` with its value, or `(on-fail)` otherwise
         validate-object-field
         #;(-> any/c (-> any/c any/c) (-> (list-of any/c) any) (-> any))
         #;(validate-list-of json proc on-success on-fail)
         ; validate that `json` is a list and map `proc` over each element. Call `on-success` with the resulting list, or `(on-fail)` otherwise
         validate-list-of)

(define (validate-cons json on-success on-fail)
  (if (cons? json)
      (on-success (car json) (cdr json))
      (on-fail)))

(define (validate-object-field json key on-success on-fail)
  (if (and (hash? json) (hash-has-key? json key))
      (on-success (hash-ref json key))
      (on-fail)))

(define (validate-list-of json proc on-success on-fail)
  (if (list? json)
      (on-success (map proc json))
      (on-fail)))

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