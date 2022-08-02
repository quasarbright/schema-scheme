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
          | (and <schema> ...+)                                   and schema
          | (: <identifier> <schema>)                             bind validation result
          | (when <schema> <racket-expr>)                         conditional check using bound validation results
          | (=> <schema> <racket-expr>)                           semantic action
<field> := (<identifier> <schema>)                                object field
|#

;; EXPANDER

; define-literal-forms makes it so you can't use the literals in any racket expressions, so you can't use "list" or "and"
; binding spaces might solve this problem, but it'd create some other ones, like with higher order schemas.
(begin-for-syntax
  (define-literal-set schema-literals
    #:datum-literals (list-of list and : when quote => cons object-has-field any equal?)
    ()))

(begin-for-syntax
  (struct schema-ref [compiled-id] #:transparent)
  (struct schema-macro [transformer] #:transparent)
  
  (define/hygienic (expand-schema stx) #:definition
    (syntax-parse stx
      #:literal-sets (schema-literals)
      [schema-name:id #:when (lookup #'schema-name schema-ref?)
                      (schema-ref-compiled-id (lookup #'schema-name schema-ref?))]
      [(macro-name:id rest ...)
       #:when (lookup #'macro-name schema-macro?)
       (define transformer (schema-macro-transformer (lookup #'macro-name schema-macro?)))
       (expand-schema (transformer stx))]
      [(list-of schema)
       (with-scope sc
         (define/syntax-parse schema^ (expand-schema (add-scope #'schema sc)))
         #'(list-of schema^))]
      [(list schema ...)
       ; this should be a macro, but it would shadow the actual list function
       (expand-schema
        (foldr (λ (first-schema rest-schema) #`(cons #,first-schema #,rest-schema))
               #'(=> (: empty any) (if (equal? '() empty) '() (error 'validate-json "expected ~a, got ~a" '() empty)))
               (syntax->list #'(schema ...))))]
      [(quote datum)
       (expand-schema #'(equal? (quote datum)))]
      [(equal? expected)
       ; don't pull this out into a macro because quote depends on it
       (expand-schema
        #'(=> (: v any)
             (let ([expected-pv expected])
               (if (equal? v expected-pv)
                   v
                   (error 'validate-json "expected ~a, got ~a" expected-pv v)))))]
      [(cons first-schema rest-schema)
       #`(cons #,(expand-schema #'first-schema) #,(expand-schema #'rest-schema))]
      [(object-has-field name:id schema)
       #`(object-has-field name #,(expand-schema #'schema))]
      [(and schema1 schema2)
       #`(and #,(expand-schema #'schema1) #,(expand-schema #'schema2))]
      [(and schema ...)
       (expand-schema
        (foldl (λ (next and-rest) #`(and #,and-rest #,next))
              #'any
              (syntax->list #'(schema ...))))]
      [(=> schema body)
       (define/syntax-parse schema^ (expand-schema #'schema))
       (define/syntax-parse body^ (local-expand #'body 'expression #f))
       #'(=> schema^ body^)]
      [(: name:id (~optional schema #:defaults ([schema #'any])))
       (define/syntax-parse schema^ (expand-schema #'schema))
       (define/syntax-parse name^ (bind! #'name (racket-var)))
       #'(: name^ schema^)]
      [(when schema body)
       (define/syntax-parse schema^ (expand-schema #'schema))
       (define/syntax-parse body^ (local-expand #'body 'expression #f))
       #'(when schema^ body^)]
      ; special case
      [any #'any]
      [schema-name:id
       ; unbound var
       (raise-syntax-error #f "unbound schema reference" #'schema-name)]
      [(macro-name:id rest ...)
       ; unbound macro
       (raise-syntax-error #f "unbound variable reference" #'macro-name)])))

;; INTERFACE MACROS

(define-syntax (define-schema stx)
  (syntax-parse stx
    [(_ name:id schema)
     ; single scope for whole schema
     (define/syntax-parse schema^ (with-scope sc (expand-schema (add-scope #'schema sc))))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     #'(begin
         (define (name-compiled json) (schema-compiled json))
         (define-syntax name (schema-ref #'name-compiled)))]))

(define-syntax (validate-json stx)
  (syntax-parse stx
    [(_ schema json:expr)
     (define/syntax-parse schema^ (with-scope sc (expand-schema (add-scope #'schema sc))))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     (define/syntax-parse json^ (local-expand #'json 'expression '()))
     #'(schema-compiled json^)]))

(define-syntax define-schema-syntax
  (syntax-parser
    [(_ macro-name:id transformer ...+)
     ; just wrap the transformer function in schema-macro
     #'
     (define-syntax macro-name
       (schema-macro transformer ...))]
    [(_ (macro-name:id args ...) body ...+)
     #'(define-schema-syntax macro-name (λ (args ...) body ...))]))

;; CORE

; a compiled schema is a
#;(-> jsexpr? any)
; returns the result of validating, usually just the json
; or throws an error

(define-syntax core-schema->racket
  (syntax-parser
    [(_ schema) #'(λ (json-v) (validate-core schema json-v result-v result-v))]))

(define-syntax validate-core
  (syntax-parser
    ; validates the json against the schema, binds the result to result-v and returns the result of evaluating body
    [(_ schema json-v:id result-v:id body:expr)
     (syntax-parse #'schema
       #:literal-sets (schema-literals)
       [(: var:id inner-schema)
        #'(validate-core inner-schema json-v var (let ([result-v var]) body))]
       [(when inner-schema guard:expr)
        #'(validate-core inner-schema json-v result-v (if guard body (error 'validate "when guard evaluated to #f")))]
       [(=> inner-schema =>-body:expr)
        #'(validate-core inner-schema json-v ignored-v (let ([result-v =>-body]) body))]
       [any #'(let ([result-v json-v]) body)]
       [(cons first-schema rest-schema)
        #'(validate-cons json-v
                         (λ (first-v rest-v)
                                  (validate-core first-schema first-v first-result-v
                                                 (validate-core rest-schema rest-v rest-result-v
                                                                (let ([result-v (cons first-result-v rest-result-v)])
                                                                  body))))
                         (λ () (error 'validate-json "expected cons, got ~a" json-v)))]
       [(list-of element-schema)
        #'(validate-list-of json-v
                            (λ (element) (validate-core element-schema element element-result-v element-result-v))
                            (λ (result-v) body)
                            (λ () (error 'validate-json "expected a list, got ~a" json-v)))]
       [(object-has-field field-name:id field-schema)
        #'(validate-object-field json-v
                                 'field-name
                                 (λ (field-result-v) (validate-core field-schema field-result-v result-v body))
                                 (λ () (error 'validate-json "expected an object with a field ~a, got ~a" 'field-name json-v)))]
       [(and schema1 schema2)
        #'(validate-core schema1 json-v ignored-v (validate-core schema2 json-v result-v body))]
       ; schemas are compiled to (-> any/c any) procedures
       [schema-ref:id #'(let ([result-v (schema-ref json-v)]) body)])]))

;; BUILT-IN SCHEMAS

; a private helper for defining atomic schemas in terms of other schemas
(define-syntax-rule
  (define-atomic-schema name predicate description)
  (define-schema name (=> (: json any) (if (predicate json) json (error 'validate-json "expected ~a, got ~a" description json)))))

(define-atomic-schema number number? "a number")
(define-atomic-schema boolean boolean? "a boolean")
(define-atomic-schema string string? "a string")
(define-atomic-schema null (λ (json) (equal? json 'null)) "null")

;; BUILT-IN SCHEMA MACROS

(define-schema-syntax object
  (syntax-parser
    [(object (name:id (~optional schema #:defaults ([schema #'any]))) ...)
     (define/syntax-parse (name^ ...) (generate-temporaries #'(name ...)))
     #'(=> (and (=> (: obj any) (if (hash? obj) obj (error 'validate-json "expected object, got ~a" obj)))
                (object-has-field name (: name^ schema))
                ...)
           (make-immutable-hasheq (list (cons 'name name^) ...)))]))

(define-schema-syntax object-bind
  (syntax-parser
    [(_ [name (~optional schema #:defaults ([schema #'any]))] ...)
     #'(object [name (: name schema)] ...)]))

(define-schema-syntax ?
  (syntax-parser
    [(_ test) #'(when (: json any) (test json))]
    [(_ test schema ...) #'(and (? test) schema ...)]))

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
  ; can't do recursive definitions yet due to how definitions are expanded
  #;(define-schema rose (list-of rose))
  #;(check-equal? (validate-schema rose '(() () ((() ())))) '(() () ((() ()))))
  ; shadow built-in
  (check-equal? (local [(define-schema number boolean)] (validate-json number #t)) #t)
  (check-equal? (validate-json (list number) '(1)) '(1))
  (check-equal? (validate-json (when (: x number) (even? x)) 2) 2)
  (check-equal? (validate-json (when (list (: x number)) (even? x)) '(2)) '(2))
  (check-equal? (validate-json (=> (list (: x number)  (: y number)) (list y x)) '(1 2)) '(2 1))
  (check-equal? (validate-json (=> (list (: x (=> (: n number) (* 5 n)))  (: y number))
                                  (list x n y))
                              '(3 7))
                '(15 3 7))
  ; side note: allowing nested when and semantic actions leads to hard-to-read schemas
  (check-equal? (validate-json (when (cons (? (λ (v) (= v 1)))
                                           (: after-1
                                              (when (cons (: second-number number) (list))
                                                (even? second-number))))
                                (and (= 2 second-number) (equal? '(2) after-1))) '(1 2))
                '(1 2))
  ; shadowing doesn't work, I assume because bind! prevents shadowing with the same scopes
  #;(check-equal? (validate-json (=> (list (: x number) (: x number))
                                  x)
                              '(1 2))
                2)
  #;(check-equal? (validate-json (=> (: x (=> (: x (: y number)) (list x y))) (list x y)) '(1 2)) '((1 2) 2))
  (local [(define-schema-syntax let
            (syntax-parser
              [(_ ([x:id schema] ...) body ...+)
               #'(=> (and (: x schema) ...) body ...)]))
          (define-schema foo (let ([x number] [y (=> any 2)]) (list x y)))]
    (check-equal? (validate-json foo 1) (list 1 2)))
  (local [(define-schema-syntax (let stx)
            (syntax-parse stx
              [(_ ([x:id schema] ...) body ...+)
               #'(=> (and (: x schema) ...) body ...)]))
          (define-schema foo (let ([x number] [y (=> any 2)]) (list x y)))]
    (check-equal? (validate-json foo 1) (list 1 2)))
  (local [(define-schema-syntax mylist
            (syntax-parser
              [(_) #'(list)]
              [(_ schema0 schema ...)
               #'(cons schema0 (mylist schema ...))]))]
    (check-equal? (validate-json (mylist number boolean null) '(1 #t null)) '(1 #t null)))
  (check-equal? (validate-json '(1 2 3) '(1 2 3)) '(1 2 3))
  (check-equal? (validate-json (equal? (list 1 2 3)) '(1 2 3)) '(1 2 3))
  (check-equal? (validate-json (=> (object-bind [x number] [y]) (list x y)) (hasheqv 'x 1 'y 'null)) '(1 null))
  ; shadow built-in with macro
  (local [(define-schema-syntax : (syntax-parser [(_ rest ...) #'number]))] (check-equal? (validate-json (:) 1) 1))
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
  (check-exn exn:fail? (thunk (validate-json (? odd? boolean) 1)))
  (check-equal? (validate-json number 1) 1)
  (check-exn exn:fail?
             (thunk (validate-json (when (cons (? (λ (v) (= v 1)))
                                               (: after-1
                                                  (when (cons (: second-number number) (list))
                                                    (even? second-number))))
                                    (and (= 2 second-number) (equal? "something else" after-1))) '(1 2))))
  (check-exn exn:fail? (thunk (validate-json '(1 2 3) '())))
  (check-exn exn:fail? (thunk (validate-json (equal? (list 1 2 3)) '()))))

