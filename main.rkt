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
<field> := (<identifier> <schema>)                                object field
|#

; side note: allowing nested when and semantic actions leads to hard-to-read schemas

;; EXPANDER

; define-literal-forms makes it so you can't use the literals in any racket expressions, so you can't use "list" or "and"
(begin-for-syntax
  (define-literal-set schema-literals
    #:datum-literals (string number boolean null list-of list object and ? : when quote => cons object-has-field any)
    ()))

(begin-for-syntax
  (struct schema-ref [compiled-id] #:transparent)
  (define/hygienic (expand-schema stx) #:definition
    (syntax-parse stx
      #:literal-sets (schema-literals)
      [schema-name:id #:when (lookup #'schema-name schema-ref?)
                      (schema-ref-compiled-id (lookup #'schema-name schema-ref?))]
      [(list-of schema)
       (with-scope sc
         (define/syntax-parse schema^ (expand-schema (add-scope #'schema sc)))
         #'(list-of schema^))]
      [(list schema ...)
       (expand-schema
        (foldr (λ (first-schema rest-schema) #`(cons #,first-schema #,rest-schema))
               #'(=> (: empty any) (if (equal? '() empty) '() (error 'validate-json "expected ~a, got ~a" '() empty)))
               (syntax->list #'(schema ...))))]
      [(cons first-schema rest-schema)
       #`(cons #,(expand-schema #'first-schema) #,(expand-schema #'rest-schema))]
      [(object (name:id schema) ...)
       (expand-schema #'(=> (and (=> (: obj any) (if (hash? obj) obj (error 'validate-json "expected object, got ~a" obj)))
                                 (object-has-field name (: name schema))
                                 ...)
                            (make-immutable-hasheq (list (cons 'name name) ...))))]
      [(object-has-field name:id schema)
       #`(object-has-field name #,(expand-schema #'schema))]
      [(and schema1 schema2)
       #`(and #,(expand-schema #'schema1) #,(expand-schema #'schema2))]
      [(and schema ...)
       (expand-schema
        (foldl (λ (next and-rest) #`(and #,and-rest #,next))
              #'any
              (syntax->list #'(schema ...))))]
      [(? test:expr)
       (define/syntax-parse test^ (local-expand #'test 'expression #f))
       #'(when (: json any) (test^ json))]
      [(? test:expr schema ...)
       (expand-schema #'(and (? test) schema ...))]
      [(=> schema body)
       (define/syntax-parse schema^ (expand-schema #'schema))
       (define/syntax-parse body^ (local-expand #'body 'expression #f))
       #'(=> schema^ body^)]
      [(: name:id schema)
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
       (raise-syntax-error #f "unbound schema reference" #'schema-name)])))

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

;; CORE

; a compiled schema is a
#;(-> jsexpr? any)
; returns the result of validating, usually just the json
; or throws an error

#|
(define-schema name schema)
compiles to (define (name json) ...)
so schema references compile to procedure applications, nothing fancy
|#

#;(define-schema name
    (when (list (: x number))
      (even? x)))
#|
when is checked
  list is checked
    : is checked
      number is checked
      result of number is bound to x
  result of list is bound to when-result
  test is ran
  result of list is returned
|#
#;
(define (name json)
  (unless (list? json) (error))
  (unless (<= 1 (length json)) (error))
  (define first-json (first json))
  (unless (number? first-json) (error))
  (define number-result first-json)
  (define x number-result)
  (define list-result (list number-result))
  (unless (even? x) (error))
  (define when-result list-result)
  when-result)
#|
hygiene should prevent accidental recursive definitions but it's still going to be tough
could rely on an invariant like "the answer goes in RAX", or pass down some kind of on-success, whether that's a variable to bind to or a procedure
might want to just compile to CPS

It's going to be tough to get those bindings

binding behavior of (list-of (: x number))?
can't just naively bind to the whole list
(list-of (when (:x number) (even? x)))
ideally it'd be bound to the element inside and the list outside. That'd be hard to do though.
bind to last occurrence?
list-of creates a new scope? That's probably a good option for now
try extending minimatch with a similar pattern
"when" and semantic actions only at top-level and then bind to list? Then it's basically match with semantic actions in every pattern.

might need to change hygeienic context to 'definition
|#
#;
(define-syntax compile
  ; invariants:
  ; the generated code binds result-pv to the result of validating the schema
  ; the generated code has all ":"-bound variables in scope at top-level, bound to the result of validating its corresponding schema
  
  ; the whole thing compiles to a flat list of defines to implement scope properly
  (syntax-parser
    #:literals ...
    [(_ number json-pv:id result-pv:id)
     ; begins shouldn't be a problem because they just splice exprs in
     #'(begin
         (unless (number? json-pv) (error))
         (define result-pv json-pv))]
    ; just single-element list for now
    ; to do multi-element, you might want to make a cons schema in core lol.
    [(_ (list schema) json-pv:id result-pv:id)
     #'(begin
         (unless (list? json-pv) (error))
         (unless (= 1 (length json-pv)) (error))
         (define first-json-pv (first json-pv))
         (compile schema first-json-pv first-result-pv)
         (define result-pv:id (list first-result-pv)))]
    [(_ (when schema expr:expr) json-pv:id result-pv:id)
     #'(begin
         (compile schema json-pv result-pv)
         ; it's ok to have this after the final (define result-pv answer)
         (unless expr (error)))]))


#;
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

; a private helper for defining atomic schemas in terms of other schemas
(define-syntax-rule
  (define-atomic-schema name predicate description)
  (define-schema name (=> (: json any) (if (predicate json) json (error 'validate-json "expected ~a, got ~a" description json)))))

(define-atomic-schema number number? "a number")
(define-atomic-schema boolean boolean? "a boolean")
(define-atomic-schema string string? "a string")
(define-atomic-schema null (λ (json) (equal? json 'null)) "null")

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

; experimenting on an alternative compiler for : and when

; (minivalidate schema json) validate the json against the schema and returns the result of validation
(define-syntax minivalidate
  (syntax-parser
    [(_ schema json:expr)
     ; the empty let is here to introduce an internal definition context
     ; I don't know of a more direct method to do this
     #'(let ()
         (define json-pv json)
         (minivalidate* schema json-pv result-pv)
         result-pv)]))

; (minivalidate* schema json-pv result-pv) validates the json against the schema and binds the result to result-pv.
; It also binds each ":"-bound variable to the result of validating its corresponding schema
; invariants:
; - the generated code binds result-pv to the result of validating the schema
; - the generated code has all ":"-bound variables in scope at top-level, bound to the result of validating its corresponding schema
; the whole thing compiles to a flat list of defines to implement scope properly
(define-syntax minivalidate*
  (syntax-parser
    [(_ schema json-pv:id result-pv:id)
     (syntax-parse #'schema
       #:literal-sets (schema-literals)
       ; honestly, schemas like number can and shouldn't be matched for
       [schema-ref:id #:when (lookup #'schema-name schema-ref?)
                      (define schema-proc-id (schema-ref-compiled-id (lookup #'schema-name schema-ref?)))
                      #`(begin
                          (define result-pv (#,schema-proc-id json-pv)))]
       [number #'(begin
                   (unless (number? json-pv) (error 'minivalidate "expected a number" json-pv))
                   (define result-pv json-pv))]
       [(quote datum)
        #'(begin
            (define qdatum-pv (quote datum))
            (unless (equal? qdatum-pv json-pv) (error 'minivalidate "expected a particular value" qdatum-pv json-pv))
            (define result-pv json-pv))]
       [(cons first-schema rest-schema)
        #'(begin
            (unless (pair? json-pv) (error 'minivalidate "expected a non-empty list" json-pv))
            (define first-json-pv (first json-pv))
            (define rest-json-pv (rest json-pv))
            (minivalidate* first-schema first-json-pv first-result-pv)
            (minivalidate* rest-schema rest-json-pv rest-result-pv)
            (define result-pv (cons first-result-pv rest-result-pv)))]
       [(: var:id inner-schema)
        #'(begin
            (minivalidate* inner-schema json-pv result-pv)
            ; the (define result-pv ...) doesn't need to be the last statement. It is not shadowed 
            (define var result-pv))]
       [(when inner-schema test:expr)
        #'(begin
            (minivalidate* inner-schema json-pv result-pv)
            (unless test (error 'minivalidate "when guard returned #f" 'test)))]
       [(=> inner-schema action:expr)
        #'(begin
            (minivalidate* inner-schema json-pv ignored-pv)
            (define result-pv action))])]))

(module+ test
  (check-equal? (minivalidate number 1) 1)
  (check-equal? (minivalidate (cons number '()) '(1)) '(1))
  (check-equal? (minivalidate (when (: x number) (even? x)) 2) 2)
  (check-equal? (minivalidate (when (cons (: x number) '()) (even? x)) '(2)) '(2))
  (check-equal? (minivalidate (=> (cons (: x number) (cons (: y number) '())) (list y x)) '(1 2)) '(2 1))
  (check-equal? (minivalidate (=> (cons (: x (=> (: n number) (* 5 n))) (cons (: y number) '()))
                                  (list x n y))
                              '(3 7))
                '(15 3 7))
  ; side note: allowing nested when and semantic actions leads to hard-to-read schemas
  (check-equal? (minivalidate (when (cons '1 (: after-1
                                                (when (cons (: second-number number) '())
                                                  (even? second-number))))
                                (and (= 2 second-number) (equal? '(2) after-1))) '(1 2))
                '(1 2))
  (check-exn exn:fail?
             (thunk (minivalidate (when (cons '1 (: after-1
                                                    (when (cons (: second-number number) '())
                                                      (even? second-number))))
                                    (and (= 2 second-number) (equal? "something else" after-1))) '(1 2))))
  ; it fails bc duplicate binding name
  #;(check-equal? (minivalidate (=> (cons (: x number) (cons (: x number) '()))
                                  x)
                              '(1 2))
                2)
  #;(check-equal? (minivalidate (=> (: x (=> (: x (: y number)) (list x y))) (list x y)) '(1 2)) '((1 2) 2)))
