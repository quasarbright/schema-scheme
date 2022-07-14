#lang racket/base

(module+ test
  (require rackunit))

;; Notice
;; To install (from within the package directory):
;;   $ raco pkg install
;; To install (once uploaded to pkgs.racket-lang.org):
;;   $ raco pkg install <<name>>
;; To uninstall:
;;   $ raco pkg remove <<name>>
;; To view documentation:
;;   $ raco docs <<name>>
;;
;; For your convenience, we have included LICENSE-MIT and LICENSE-APACHE files.
;; If you would prefer to use a different license, replace those files with the
;; desired license.
;;
;; Some users like to add a `private/` directory, place auxiliary files there,
;; and require them in `main.rkt`.
;;
;; See the current version of the racket style guide here:
;; http://docs.racket-lang.org/style/index.html

;; Code here

#|
<racket-def> := ... | (define-schema <schema-id> <schema>)        interface macro
<racket-expr> := ... | (validate <schema-id> <racket-expr>)       interface macro
<schema-id> := <identifier>
<schema> := string | number | boolean | null                      atomic types
          | <schema-id>                                           schema reference
          | (list-of <schema>)                                    list schema
          | (object <field> ...)                                  object schema
<field> := (<identifier> <schema>)                                object field
|#
(require ee-lib)
(require ee-lib/define)
(require syntax/parse (for-syntax syntax/parse))
(require (for-syntax racket/base))
(require (for-template racket/base))
(require racket/match)

#;(define-literal-forms schema-literals "schema literal"
    (string number boolean null list-of object))

#;(begin-for-syntax
    (struct schema-var []))

#;(module schema-classes racket
  (define-syntax string (syntax-rules ()))
  (define-syntax number (syntax-rules ()))
  (define-syntax boolean (syntax-rules ()))
  (define-syntax null (syntax-rules ()))
  (define-syntax list-of (syntax-rules ()))
  (define-syntax object (syntax-rules ()))
  (provide string number boolean null list-of object))

#;(require (for-template 'schema-classes))

(begin-for-syntax
  (define-syntax-class core-schema
    #:datum-literals (string number boolean null list-of object)
    #:description "core schema"
    (pattern string)
    (pattern number)
    (pattern boolean)
    (pattern null)
    (pattern (list-of ele:core-schema))
    (pattern (object field:core-field ...)))

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

(define-syntax (core-schema->racket stx)
  (syntax-parse stx
    ; I don't want to repeat myself, but a literal set didn't seem to work
    #:datum-literals (string number boolean null list-of object/schema)
    [(_ number) #'#%number-schema]
    [(_ boolean) #'#%boolean-schema]
    [(_ string) #'#%string-schema]
    [(_ null) #'#%null-schema]
    [(_ (list-of ele-schema:core-schema)) #'(#%list-of-schema (core-schema->racket ele-schema))]
    [(_ (object (field value-schema:core-schema) ...)) #'(#%object-schema (list (list 'field (core-schema->racket value-schema)) ...))]))

(module+ test
  (check-equal? ((core-schema->racket null) 'null) 'null)
  (check-equal? ((core-schema->racket number) 1) 1)
  (check-equal? ((core-schema->racket string) "s") "s")
  (check-equal? ((core-schema->racket boolean) #t) #t)
  (check-equal? ((core-schema->racket (list-of number)) '()) '())
  (check-equal? ((core-schema->racket (list-of number)) '(1 2 3)) '(1 2 3))
  (check-equal? ((core-schema->racket (object (foo number))) (hasheq 'foo 1)) (hasheq 'foo 1))
  (check-exn exn:fail? (λ () ((core-schema->racket number) #t)))
  (check-exn exn:fail? (λ () ((core-schema->racket (list-of number)) #t)))
  (check-exn exn:fail? (λ () ((core-schema->racket (list-of number)) (list 1 2 #t)))))

#;(define-syntax (define-schema stx)
    (syntax-parse stx ))
