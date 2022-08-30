#lang racket
(require "private/core.rkt")
(require syntax/parse (for-syntax syntax/stx syntax/parse syntax/id-set syntax/id-table))
(require (for-syntax ee-lib) ee-lib/define)
(require (for-syntax racket/set))

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
          | (or <schema> ...+)                                    or schema
          | (: <identifier> <schema>)                             bind validation result
          | (when <schema> <racket-expr>)                         conditional check using bound validation results
          | (=> <schema> <racket-expr>)                           semantic action
<field> := (<identifier> <schema>)                                object field
|#

; schema validation error
(struct exn:fail:schema exn:fail ()
  #:extra-constructor-name make-exn:fail:schema
  #:transparent)

; raise a schema validation error with the given message
(define (fail-validation format-str . vs)
  (raise (make-exn:fail:schema (format "validate-json: ~a" (apply format format-str vs)) (current-continuation-marks))))

;; EXPANDER

; define-literal-forms makes it so you can't use the literals in any racket expressions, so you can't use "list" or "and"
; binding spaces might solve this problem, but it'd create some other ones, like with higher order schemas.

(begin-for-syntax
  (define-literal-set schema-literals
    #:datum-literals (list-of list and or : when quote quasiquote unquote => cons object-has-field any equal?)
    ()))

(begin-for-syntax
  (struct schema-ref [] #:transparent)
  (struct schema-macro [transformer] #:transparent)
  (define compiled-names (make-free-id-table))
  
  (define/hygienic (expand-schema stx) #:definition
    (syntax-parse stx
      #:literal-sets (schema-literals)
      [schema-name:id #:when (lookup #'schema-name schema-ref?)
                      ; the flip is necessary to get rid of the intro scope
                      ; when we define a schema, the generated code does a free-table-set!.
                      ; by the time that runs, the intro scope is flipped off. but in this macro
                      ; it's still there so we flip it off here.
                      (free-id-table-ref compiled-names (flip-intro-scope #'schema-name))]
      [(macro-name:id rest ...)
       #:when (lookup #'macro-name schema-macro?)
       (define transformer (schema-macro-transformer (lookup #'macro-name schema-macro?)))
       (expand-schema (transformer stx))]
      [(list-of schema)
       (define/syntax-parse schema^ (expand-schema #'schema))
       #'(list-of schema^)]
      [(list schema ...)
       ; this should be a macro, but it would shadow the actual list function
       (expand-schema
        (foldr (λ (first-schema rest-schema) #`(cons #,first-schema #,rest-schema))
               #'(=> (: empty any) (if (equal? '() empty) '() (fail-validation "expected ~a, got ~a" '() empty)))
               (syntax->list #'(schema ...))))]
      [(quote datum)
       (expand-schema #'(equal? (quote datum)))]
      [(unquote _)
       (raise-syntax-error 'unquote "not used in quasiquote" stx)]
      [(quasiquote qs)
       (syntax-parse #'qs
         #:literal-sets (schema-literals)
         [(unquote schema) (expand-schema #'schema)]
         [(qs ...) (expand-schema #'(list (quasiquote qs) ...))]
         [datum (expand-schema #'(quote datum))])]
      [(equal? expected)
       ; don't pull this out into a macro because quote depends on it
       (expand-schema
        #'(=> (: v any)
             (let ([expected-pv expected])
               (if (equal? v expected-pv)
                   v
                   (fail-validation "expected ~a, got ~a" expected-pv v)))))]
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
      [(or schema1 schema2)
       (define/syntax-parse schema1^ (with-scope sc (expand-schema (add-scope #'schema1 sc))))
       (define/syntax-parse schema2^ (with-scope sc (expand-schema (add-scope #'schema2 sc))))
       #'(or schema1^ schema2^)]
      [(or schema0 schema ...)
       (expand-schema
        (foldl (λ (next or-rest) #`(or #,or-rest #,next))
              #'schema0
              (syntax->list #'(schema ...))))]
      [(=> schema body ...+)
       (define/syntax-parse schema^ (expand-schema #'schema))
       (define/syntax-parse body^ (local-expand #'(let () body ...) 'expression '() (current-def-ctx)))
       #'(=> schema^ body^)]
      [(: name:id (~optional schema #:defaults ([schema #'any])))
       (define/syntax-parse schema^ (expand-schema #'schema))
       (define/syntax-parse name^ (bind! #'name (racket-var)))
       #'(: name^ schema^)]
      [(when schema body ...+)
       (define/syntax-parse schema^ (expand-schema #'schema))
       (define/syntax-parse body^ (local-expand #'(let () body ...) 'expression '() (current-def-ctx)))
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

(define-syntax schema-rhs
  (syntax-parser
    [(_ schema)
     ; single scope for whole schema
     (define/syntax-parse schema^ (with-scope sc (expand-schema (add-scope #'schema sc))))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     #'schema-compiled]))

#;(phase-1-effect body)
; runs 'body' every visit if we're in a module, or only once if we're in a local def ctx.
; necessary for providing/requiring schemas to work properly
(define-syntax (phase-1-effect stx)
  (syntax-case stx ()
    [(_ e)
     (if (eq? (syntax-local-context) 'module)
      #'(begin-for-syntax e); this will run 'e' every visit
      ; this will run 'e' once during the module's expansion
      (let ()
        (define def-ctx (syntax-local-make-definition-context))
        (syntax-local-bind-syntaxes (list #'x) #'(begin e 5) def-ctx)
        #'(begin)))]))

(define-syntax (define-schema stx)
  (syntax-parse stx
    [(_ name:id schema)
     #'(begin
         (define (name-compiled json) ((schema-rhs schema) json))
         (define-syntax name (schema-ref))
         (phase-1-effect
           (free-id-table-set! compiled-names #'name #'name-compiled)))]))

(define-syntax (validate-json stx)
  (syntax-parse stx
    [(_ schema json:expr)
     (define/syntax-parse schema^ (with-scope sc (expand-schema (add-scope #'schema sc))))
     (define/syntax-parse schema-compiled #'(core-schema->racket schema^))
     #'(schema-compiled json)]))

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
        #'(validate-core inner-schema json-v result-v (if guard body (fail-validation "when guard evaluated to #f")))]
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
                         (λ () (fail-validation "expected cons, got ~a" json-v)))]
       [(list-of element-schema)
        (define vars-set (bound-schema-vars #'element-schema))
        (define/syntax-parse (var ...) (set->list vars-set))
        (define/syntax-parse (var-list-outer ...) (generate-temporaries #'(var ...)))
        (define/syntax-parse (var-list-inner ...) (generate-temporaries #'(var ...)))
        #'(if (list? json-v)
              (let-values ([(results var-list-outer ...)
                            (for/fold ([results '()] [var-list-inner '()] ...)
                                      ([element json-v])
                              (validate-core element-schema element element-result
                                             (values (cons element-result results) (cons var var-list-inner) ...)))])
                (let ([result-v (reverse results)]
                      [var (reverse var-list-outer)]
                      ...)
                  body))
              (fail-validation "expected a list, got ~a" json-v))]
       [(object-has-field field-name:id field-schema)
        #'(validate-object-field json-v
                                 'field-name
                                 (λ (field-result-v) (validate-core field-schema field-result-v result-v body))
                                 (λ () (fail-validation "expected an object with a field ~a, got ~a" 'field-name json-v)))]
       [(and schema1 schema2)
        #'(validate-core schema1 json-v ignored-v (validate-core schema2 json-v result-v body))]
       [(or schema1 schema2)
        ; 'body' doesn't have access to anything bound in 'or'
        #'(let ([body-proc (λ (result-v) body)])
            (with-handlers ([exn:fail:schema? (λ (e) (validate-core schema2 json-v result-v (body-proc result-v)))])
              (validate-core schema1 json-v result-v (body-proc result-v))))]
       ; schemas are compiled to (-> any/c any) procedures
       [schema-ref:id #'(let ([result-v (schema-ref json-v)]) body)])]))

(begin-for-syntax
  (define (bound-schema-vars stx)
    (syntax-parse stx
      #:literal-sets (schema-literals)
      [(: var:id schema)
       (set-add (bound-schema-vars #'schema) #'var)]
      [var:id (immutable-bound-id-set)]
      ; it has a separate scope
      [(list-of schema) (bound-schema-vars #'schema)]
      [(cons schema1 schema2) (apply set-union (immutable-bound-id-set) (stx-map (λ (stx) (bound-schema-vars stx)) #'(schema1 schema2)))]
      [(object-has-field field schema) (bound-schema-vars #'schema)]
      [(and schema ...) (bound-schema-vars* #'(schema ...))]
      [(or schema ...) (immutable-bound-id-set)]
      [(=> schema body ...) (bound-schema-vars #'schema)]
      [(when schema body ...) (bound-schema-vars #'schema)]
      [any (immutable-bound-id-set)]))

  ; unions bound vars of a list of schemas
  (define/hygienic (bound-schema-vars* stx) #:definition
    (syntax-parse stx
      [(schema ...) (apply set-union (immutable-bound-id-set) (stx-map (λ (stx) (bound-schema-vars stx)) #'(schema ...)))])))


;; BUILT-IN SCHEMAS

; a private helper for defining atomic schemas in terms of other schemas
(define-syntax-rule
  (define-atomic-schema name predicate description)
  (define-schema name (=> (: json any) (if (predicate json) json (fail-validation "expected ~a, got ~a" description json)))))

(define-atomic-schema number number? "a number")
(define-atomic-schema boolean boolean? "a boolean")
(define-atomic-schema string string? "a string")
(define-atomic-schema null (λ (json) (equal? json 'null)) "null")

;; BUILT-IN SCHEMA MACROS

(define-schema-syntax object
  (syntax-parser
    [(object (name:id (~optional schema #:defaults ([schema #'any]))) ...)
     (define/syntax-parse (name^ ...) (generate-temporaries #'(name ...)))
     #'(=> (and (=> (: obj any) (if (hash? obj) obj (fail-validation "expected object, got ~a" obj)))
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
  ; recursive definition
  (define-schema rose (list-of rose))
  (check-equal? (validate-json rose '(() () ((() ())))) '(() () ((() ()))))
  ; mutually recursive definition
  ; this should actually work, there is a bug with 'or'
  #;(define-schema odd-length-list (cons any even-length-list))
  #;(define-schema even-length-list (or '() (cons any odd-length-list)))
  #;(check-equal? (validate-json even-length-list '()) '())
  #;(check-equal? (validate-json odd-length-list '(1)) '(1))
  #;(check-equal? (validate-json odd-length-list '(1 2 3)) '(1 2 3))
  #;(check-exn exn:fail:schema? (thunk (validate-json odd-length-list '())))
  ;(check-exn exn:fail:schema? (thunk (validate-json odd-length-list '(1 2))))
  (define-schema mutl (list-of muto))
  (define-schema muto (object [mutl mutl]))
  (check-equal? (validate-json mutl '()) '())
  (check-equal? (validate-json muto (hasheq 'mutl '())) (hasheq 'mutl '()))
  (check-equal? (validate-json mutl (list (hasheq 'mutl '()) (hasheq 'mutl '())))
                (list (hasheq 'mutl '()) (hasheq 'mutl '())))
  (check-exn exn:fail:schema? (thunk (validate-json mutl (list (hasheq 'mutl 1)))))
  ; shadow built-in
  (check-equal? (let () (define-schema number boolean) (#%expression (validate-json number #t))) #t)
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
  #;(check-equal? (validate-json (=> (: x (=> (: x (: y number)) (list x y))) (list x y)) 1) '((1 1) 1))
  (let ()
    (define-schema-syntax let
      (syntax-parser
        [(_ ([x:id schema] ...) body ...+)
         #'(=> (and (: x schema) ...) body ...)]))
    (define-schema foo (let ([x number] [y (=> any 2)]) (list x y)))
    (check-equal? (validate-json foo 1) (list 1 2)))
  (let ()
    (define-schema-syntax (let stx)
      (syntax-parse stx
        [(_ ([x:id schema] ...) body ...+)
         #'(=> (and (: x schema) ...) body ...)]))
    (define-schema foo (let ([x number] [y (=> any 2)]) (list x y)))
    (check-equal? (validate-json foo 1) (list 1 2)))
  (let ()
    (define-schema-syntax mylist
      (syntax-parser
        [(_) #'(list)]
        [(_ schema0 schema ...)
         #'(cons schema0 (mylist schema ...))]))
    (check-equal? (validate-json (mylist number boolean null) '(1 #t null)) '(1 #t null)))
  (check-equal? (validate-json '(1 2 3) '(1 2 3)) '(1 2 3))
  (check-equal? (validate-json (equal? (list 1 2 3)) '(1 2 3)) '(1 2 3))
  (check-equal? (validate-json (=> (object-bind [x number] [y]) (list x y)) (hasheqv 'x 1 'y 'null)) '(1 null))
  ; shadow built-in with macro
  (let () (define-schema-syntax : (syntax-parser [(_ rest ...) #'number])) (check-equal? (validate-json (:) 1) 1))
  (check-exn exn:fail:schema? (thunk (validate-json number 'null)))
  (check-exn exn:fail:schema? (thunk (validate-json boolean 'null)))
  (check-exn exn:fail:schema? (thunk (validate-json string 'null)))
  (check-exn exn:fail:schema? (thunk (validate-json null #t)))
  (check-exn exn:fail:schema? (thunk (validate-json (list-of boolean) 'null)))
  (check-exn exn:fail:schema? (thunk (validate-json (list-of boolean) (list #t 'null))))
  (check-exn exn:fail:schema? (thunk (validate-json (list number boolean) 'null)))
  (check-exn exn:fail:schema? (thunk (validate-json (list number boolean) '())))
  (check-exn exn:fail:schema? (thunk (validate-json (list number boolean) '(1 #t 1))))
  (check-exn exn:fail:schema? (thunk (validate-json (list number boolean) '(#t 1))))
  (check-exn exn:fail:schema? (thunk (validate-json (object) 'null)))
  (check-exn exn:fail:schema? (thunk (validate-json (object (foo number)) 'null)))
  (check-exn exn:fail:schema? (thunk (validate-json (object (foo number)) (hasheq))))
  (check-exn exn:fail:schema? (thunk (validate-json (object (foo number)) (hasheq 'foo #t))))
  (check-exn exn:fail:schema? (thunk (validate-json (object (foo number)) (hasheq 'bar 1))))
  (check-exn exn:fail:schema? (thunk (validate-json (? odd?) 2)))
  (check-exn exn:fail:schema? (thunk (validate-json (? odd? boolean) 1)))
  (check-equal? (validate-json number 1) 1)
  (check-exn exn:fail:schema?
             (thunk (validate-json (when (cons (? (λ (v) (= v 1)))
                                               (: after-1
                                                  (when (cons (: second-number number) (list))
                                                    (even? second-number))))
                                    (and (= 2 second-number) (equal? "something else" after-1))) '(1 2))))
  (check-exn exn:fail:schema? (thunk (validate-json '(1 2 3) '())))
  (check-exn exn:fail:schema? (thunk (validate-json (equal? (list 1 2 3)) '())))

  (check-equal? (validate-json (or number boolean) 1) 1)
  (check-equal? (validate-json (or number boolean) #t) #t)
  (check-equal? (validate-json (or (=> number 'num) (=> boolean 'bool)) #t)
                'bool)
  (check-exn exn:fail:schema? (thunk (validate-json (or number boolean) 'null)))
  (check-equal? (validate-json (or number boolean null) 'null) 'null)
  ; fails bc it thinks it's duplicate bindings bc single scope
  (check-equal? (validate-json (or (: x number) (: x boolean)) 1) 1)
  (check-equal? (validate-json (or (: x number) (: x boolean)) #t) #t)
  ; this fails because equal? compiles to a semantic action which binds a variable, which 'or' thinks
  ; is bound by the user. This causes 'or's same-bindings check to fail even though the user defined
  ; no bindings. I shouldn't have to change the compilation of equal?. Rather, I should make the
  ; 'or' check account for hygiene and macro-introduced bindings.
  (check-equal? (validate-json (or (equal? #t) number) 1) 1)
  ; bindings in an 'or' aren't in scope outside of the 'or'
  (check-equal? (validate-json (=> (and (: x any) (or (list (: x any) (: y any)) any)) x) '(1 2))
                '(1 2))
  ; branches of an 'or' can have different sets of bindings
  (check-equal? (validate-json (or (list (: x any) (: y any)) (list (: a any) (: b any))) '(1 2))
                '(1 2))
  (test-equal? "=> has an implicit begin"
               (validate-json (=> any (define x 2) x) #t)
                2)
  (test-equal? "when has an implicit begin"
               (validate-json (when any (define x #t) x) 2)
               2)
  (test-equal? "basic quasiquote works"
               (validate-json `(#t 2 ,number ,(=> any 'ignored))
                              '(#t 2 3 null))
               '(#t 2 3 ignored))
  (test-equal? "quasiquote only has depth 1"
               ; if qq supported depth >1, the variabele bind schema would not be validated against
               (validate-json (=> `(1 `,(: x any) 3) x)
                              '(1 `2 3))
               2)
  (test-equal? "list-of supports internal use of variables"
               (validate-json (list-of (=> (: a) (- a))) '(1 2 3))
               '(-1 -2 -3))
  (test-equal? "list-of supports external use of variables"
               (validate-json (=> (list-of (: a any)) a) '(1 2 3))
               '(1 2 3))
  (test-equal? "list-of supports external use of deep inner variables"
               (validate-json (=> (list-of (list (: a any) (: b any))) (list a b)) '((1 2) (3 4) (5 6)))
               '((1 3 5) (2 4 6))))
