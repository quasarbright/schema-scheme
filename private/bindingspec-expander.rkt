#lang racket

(module+ test (require rackunit))
(provide (all-defined-out)
         (for-space schema-scheme (all-defined-out)))

(require bindingspec (for-syntax syntax/parse racket/set syntax/id-set syntax/stx))

; schema validation error
(struct exn:fail:schema exn:fail ()
  #:extra-constructor-name make-exn:fail:schema
  #:transparent)

; raise a schema validation error with the given message
(define (fail-validation format-str . vs)
  (raise (make-exn:fail:schema (format "validate-json: ~a" (apply format format-str vs)) (current-continuation-marks))))

(define-hosted-syntaxes

  (binding-class var #:description "schema-bound variable")
  (binding-class schema-ref
                 #:description "schema reference"
                 ; TODO this caused failing persistent-free-id-table-set! on definitions. Why?
                 #;#;#:binding-space schema-scheme)
  (extension-class schema-macro
                   #:description "schema macro"
                   #:binding-space schema-scheme)

  (nonterminal schema-top
               s:schema
               #:binding
               {(nest-one s [])})

  (nesting-nonterminal schema (tail)
                       #:description "schema"
                       #:allow-extension schema-macro
                       #:binding-space schema-scheme
                       v:schema-ref
                       #:binding {tail}
                       (bind v:var s:schema)
                       #:binding (nest-one s {(bind v) tail})
                       (=> s:schema body:expr)
                       #:binding (nest-one s (host body))
                       ;#:binding [(nest-one s (host body)) (nest-one s tail)]
                       ; ^ this caused a failed persistent-free-id-table-ref for some reason.
                       ; for now, => and 'when' have their own scopes.
                       ; TODO ask michael about it
                       (when s:schema guard:expr)
                       #:binding (nest-one s (host guard))
                       ;#:binding [(nest-one s (host guard)) (nest-one s tail)]
                       (object-has-field name:id s:schema)
                       #:binding (nest-one s tail)
                       (cons car-schema:schema cdr-schema:schema)
                       #:binding (nest-one car-schema (nest-one cdr-schema tail))
                       (? valid?:expr desc:expr)
                       #:binding [(host valid?) (host desc) tail]
                       (or2 s1:schema s2:schema)
                       #:binding [(nest-one s1 []) (nest-one s2 [])]
                       ; for some reason, using 'fail' doesn't work.
                       ; using a fail schema says it's not a schema.
                       (#%fail msg:expr)
                       #:binding [(host msg) tail]
                       (and2 s1:schema s2:schema)
                       #:binding [(nest-one s1 (nest-one s2 tail))]
                       (listof s:schema)
                       #:binding [(nest-one s tail)]))

(define-syntax define-schema-scheme-syntax
  (syntax-parser
    [(_ name:id rhs:expr)
     #:with spaced-name ((make-interned-syntax-introducer 'schema-scheme) (attribute name) 'add)
     #'(define-syntax spaced-name rhs)]))

(define-syntax define-schema-syntax
  (syntax-parser
    [(_ (macro-name:id args ...) body ...) #'(define-schema-syntax macro-name (λ (args ...) body ...))]
    [(_ macro-name:id transformer) #'(define-schema-scheme-syntax macro-name (schema-macro transformer))]))

; TODO this duplicates the value expression, but I'm not sure if it's possible to avoid and have a good description
(define-schema-syntax equal? (syntax-rules () [(equal? val) (? (λ (json) (equal? json val)) val)]))
(define-schema-syntax quote (syntax-rules  () [(quote datum) (equal? (quote datum))]))
(define-schema-syntax list (syntax-rules () [(list) '()] [(list p0 p ...) (cons p0 (list p ...))]))
; simple quasiquote schema
; max depth of 1, no splicing unquote, only supports list quasi-schemas
(define-schema-syntax quasiquote (syntax-rules (unquote)
                                   [(quasiquote (unquote schema)) schema]
                                   [(quasiquote (schema ...)) (list (quasiquote schema)  ...)]
                                   [(quasiquote datum) 'datum]))
(define-schema-syntax or (syntax-rules ()
                           [(or) (fail "all cases of 'or' failed")]
                           [(or schema0 schema ...) (or2 schema0 (or schema ...))]))
; alias for #%fail
(define-schema-syntax fail (syntax-rules () [(fail e ...) (#%fail e ...)]))
(define-schema-syntax and (syntax-rules ()
                            [(and) any]
                            ; this is necessary to ensure that the result of the 'and' is
                            ; the result of the last schema
                            [(and schema) schema]
                            [(and schema0 schema ...) (and2 schema0 (and schema ...))]))
; TODO this uses =>, so bindings inside this schema are not in scope outside of it
(define-schema-syntax object
  (syntax-parser
    [(object [field-name:id (~optional schema #:defaults ([schema #'any]))] ...)
     ; it is necessary to generate temporaries so the introduced bindings aren't usable outside of this schema.
     ; since the user supplies field-name ..., they won't get macro intro scope.
     #:with (field-name^ ...) (generate-temporaries (attribute field-name))
     #'(=> (and (object-has-field field-name (bind field-name^ schema)) ...)
           (make-immutable-hasheq (list (cons 'field-name field-name^) ...)))]))
(define-schema-syntax let
  (syntax-parser
    [(let ([var:id schema] ...)
       body)
     #'(=> (and (bind var schema) ...)
           body)]))

(define-host-interface/definition (define-schema name:schema-ref s:schema-top)
  #:binding (export name)
  ->
  (define
    [(compile-binder! #'name)]
    [(compile-schema #'s)]))

(define-schema number (? number? "a number"))
(define-schema string (? string? "a string"))
(define-schema boolean (? boolean? "a boolean"))
(define-schema null 'null)
(define-schema any (? (const #t) "anything"))

(define-host-interface/expression (validate-json s:schema-top json:expr)
  #:binding [s (host json)]
  #:with s^ (compile-schema #'s)
  #'(s^ json))

(begin-for-syntax
  (define-literal-set schema-literals
    ; TODO binding-spaced non-datum literals
    #:datum-literals (listof list and2 or2 bind when => cons object-has-field ? #%fail)
    ())

  (define (compile-schema schema)
    #`(λ (json [on-fail #f])
        (let ([on-fail (or on-fail (λ ([msg "validation failed"]) (fail-validation msg)))])
          #,(compile-validate schema #'json #'result #'result #'on-fail))))
  ; on-fail is syntax for an identifier bound to a (-> [string?] any) which takes in an optional error message and, if there are no other schemas to try, errors out.
  ; 'json' and 'result' must be identifiers.
  ; the output is syntax that validates 'json' against 'schema' and binds the result of validating to 'result' in 'body',
  ; or calls 'on-fail' with an error message.
  (define (compile-validate schema json result body on-fail)
    (syntax-parse (list schema json result body on-fail)
      [(schema json:id result:id body on-fail:id)
       (syntax-parse #'schema
         #:literal-sets (schema-literals)
         [(bind var:id schema)
          #:with var^ (compile-binder! #'var)
          (compile-validate #'schema #'json #'result #'(let ([var^ result]) body) #'on-fail)]
         [(when schema guard)
          (compile-validate #'schema #'json #'result
                            #`(if #,(compile-host-expr #'guard) body (on-fail "'when' guard evaluated to #f"))
                            #'on-fail)]
         [(=> schema action)
          (compile-validate #'schema #'json #'ignored
                            #`(let ([result #,(compile-host-expr #'action)]) body)
                            #'on-fail)]
         [(object-has-field name:id schema)
          ; this shouldn't be necessary, but I'm paranoid bc this compiler doesn't get intro scopes
          #:with (field) (generate-temporaries (list #'field))
          #`(if (and (hash? json) (hash-has-key? json 'name))
                (let ([field (hash-ref json 'name)])
                  #,(compile-validate #'schema #'field #'result #'body #'on-fail))
                (on-fail (format "expected an object, but got ~v" json)))]
         [(cons car-schema cdr-schema)
          ; since this compiler isn't a macro, we don't get intro scopes!
          ; this causes introduced variables of nested conses to shadow each other,
          ; so we need to generate temporaries to avoid shadowing.
          #:with (car-value cdr-value) (generate-temporaries (list #'car-value #'cdr-value))
          #:with (car-result cdr-result) (generate-temporaries (list #'car-result #'cdr-result))
          #`(if (cons? json)
                (let ([car-value (car json)]
                      [cdr-value (cdr json)])
                  #,(compile-validate #'car-schema #'car-value #'car-result
                                      (compile-validate #'cdr-schema #'cdr-value #'cdr-result
                                                        #'(let ([result (cons car-result cdr-result)])
                                                            body)
                                                        #'on-fail)
                                      #'on-fail))
                (on-fail (format "expected a cons, but got ~v " json)))]
         [(? valid? desc)
          #`(if (#,(compile-host-expr #'valid?) json)
                (let ([result json]) body)
                (on-fail (format "expected ~a, but got ~v" #,(compile-host-expr #'desc) json)))]
         [schema-ref:id
          #`(let ([result (#,(compile-reference #'schema-ref) json on-fail)]) body)]
         [(or2 schema1 schema2)
          #:with new-on-fail #`(λ _ #,(compile-validate #'schema2 #'json #'result
                                                        #'(body-proc result)
                                                        #'on-fail))
          ; 'body' shouldn't have access to anything bound in 'or'
          #`(let* ([body-proc (λ (result) body)]
                   [on-fail new-on-fail])
              #,(compile-validate #'schema1 #'json #'result #'(body-proc result) #'on-fail))]
         [(#%fail msg) #`(on-fail #,(compile-host-expr #'msg))]
         [(and2 schema1 schema2)
          (compile-validate #'schema1 #'json #'ignored
                            (compile-validate #'schema2 #'json #'result #'body #'on-fail)
                            #'on-fail)]
         ; TODO handle inner bindings
         [(listof schema)
          (define bound-vars-set (get-schema-bound-vars #'schema))
          (define/syntax-parse (var ...) (set->list bound-vars-set))
          ; this causes compile-binder! to run twice. once here, once in the compilation
          ; you can either take in a mapping of binders to their compiled versions
          ; or return a set of bound ids in addition to the output stx in compile-validate.
          ; or you could just not expose variables bound in listof.
          ; or you could make a safe compile-binder!, run this map after compiling the element stuff, and use
          ; the safe variant here.
          ; or you could make a pass that just does compile-binder! on everything.
          ; all options suck
          (define/syntax-parse (var-bind ...) (stx-map compile-binder! (attribute var)))
          (define/syntax-parse (var-ref ...) (stx-map compile-reference (attribute var)))
          (define/syntax-parse (var-list-bind ...) (generate-temporaries (attribute var)))
          (define/syntax-parse (var-list-ref ...) (generate-temporaries (attribute var)))
          ; just to simulate introduction scopes to be safe
          (with-syntax ([(results) (generate-temporaries (list #'results))]
                        [(element) (generate-temporaries (list #'element))]
                        [(element-result) (generate-temporaries (list #'element-result))])
            #`(if (list? json)
                  (let/cc k
                    (let ([on-fail-k (λ args (k (apply on-fail args)))])
                      (let-values ([(results var-bind ...)
                                    (for/fold ([results '()] [var-list-bind '()] ...)
                                              ([element json])
                                      #,(compile-validate #'schema #'element #'element-result
                                                          #'(values (cons element-result results) (cons var-ref var-list-ref) ...)
                                                          #'on-fail-k))])
                        (let ([result (reverse results)]
                              [var-bind (reverse var-list-ref)]
                              ...)
                          body))))
                  (on-fail (format "expected a list, but got ~v" json))))])]))

  ; returns a bound-id-set of all vars bound in the schema according to the scoping rules.
  ; does not do compile-binder! or compile-reference
  (define (get-schema-bound-vars schema)
    (syntax-parse schema
      #:literal-sets (schema-literals)
      [schema-ref:id (immutable-bound-id-set)]
      [(bind v:id schema) (set-add (get-schema-bound-vars #'schema) #'v)]
      ; no bound ids because they have their own scopes
      [(=> schema body) (immutable-bound-id-set)]
      [(when schema guard) (immutable-bound-id-set)]
      [(object-has-field name:id schema) (get-schema-bound-vars #'schema)]
      [(cons schema1 schema2) (set-union (get-schema-bound-vars #'schema1) (get-schema-bound-vars #'schema2))]
      [(? valid? desc) (immutable-bound-id-set)]
      [(or2 schema1 schema2) (set-union (get-schema-bound-vars #'schema1) (get-schema-bound-vars #'schema2))]
      [(#%fail msg) (immutable-bound-id-set)]
      [(and2 schema1 schema2) (set-union (get-schema-bound-vars #'schema1) (get-schema-bound-vars #'schema2))]
      [(listof schema) (get-schema-bound-vars #'schema)]))

  (define (compile-host-expr e)
    (resume-host-expansion e #:reference-compilers ([var compile-reference]))))

(module+ test
  (check-equal? (validate-json any 1) 1)
  (check-equal? (validate-json (object-has-field foo any) (hasheq 'foo 1)) 1)
  (check-exn exn:fail:schema? (thunk (validate-json (object-has-field foo any) 1)))
  (check-exn exn:fail:schema? (thunk (validate-json (object-has-field foo any) (hasheq 'bar 1))))
  (check-equal? (validate-json (=> any 2) 1) 2)
  (check-equal? (validate-json (when any #t) 1) 1)
  (check-exn exn:fail:schema? (thunk (validate-json (when any #f) 1)))
  (check-equal? (validate-json (bind x any) 1) 1)
  (check-equal? (validate-json (=> (bind y any) (list y)) 1) '(1))
  (check-equal? (validate-json (when (bind y any) (even? y)) 2) 2)
  (check-equal? (validate-json (cons any any) '(1 2)) '(1 2))
  (check-exn exn:fail:schema? (thunk (validate-json (cons any any) '())))
  (check-equal? (validate-json (=> (cons (bind x any) (bind y any)) (list x y)) '(1 2)) '(1 (2)))
  (check-equal? (validate-json (? even? "an even number") 2) 2)
  (check-exn #rx"expected an even number" (thunk (validate-json (? even? "an even number") 1)))
  (check-equal? (validate-json (equal? 2) 2) 2)
  (check-exn exn:fail:schema? (thunk (validate-json (equal? 2) 1)))
  (check-equal? (validate-json '2 2) 2)
  (check-exn exn:fail:schema? (thunk (validate-json '2 1)))
  ; regression test: outer car-result would get shadowed by inner car-result bc no intro scopes.
  ; used to result in '(2 2)
  (check-equal? (validate-json (cons any (cons any any)) '(1 2)) '(1 2))
  (check-equal? (validate-json (list any any) '(1 2)) '(1 2))
  (check-exn exn:fail:schema? (thunk (validate-json (list any any) '(1))))
  (check-exn exn:fail:schema? (thunk (validate-json (list any any) '(1 2 3))))
  (check-exn exn:fail:schema? (thunk (validate-json (list any any) '())))
  (check-equal? (validate-json (=> (list (bind a any) (bind b any)) (list b a)) '(1 2)) '(2 1))
  (check-equal? (validate-json (=> `(1 2 ,(bind x any)) x) '(1 2 3)) 3)
  (check-exn exn:fail:schema? (thunk (validate-json (=> `(1 2 ,(bind x number)) x) '(1 2 "hello"))))
  (test-equal? "schema reference"
               (validate-json number 1)
               1)
  (check-exn exn:fail:schema? (thunk (validate-json number "hello")))
  (test-equal? "or schema"
               (validate-json (or '1 '2) 1)
               1)
  (test-equal? "or schema where first fails"
               (validate-json (or '1 '2) 2)
               2)
  (test-exn "or both fail"
            exn:fail:schema?
            (thunk (validate-json (or '1 '2) 3)))
  (test-exn "fail schema"
            #rx"boom"
            ; for some reason, using 'fail' here errors out saying it's not a schema.
            ; Using it in 'or' expansion and in the repl works though. maybe something with rackunit
            (thunk (validate-json (#%fail "boom") 1)))
  (test-exn "empty or"
            #rx"all cases of 'or' failed"
            (thunk (validate-json (or) 1)))
  (test-equal? "and #t #t"
               (validate-json (and '1 (=> any 2)) 1)
               2)
  (test-exn "and #t #f"
            exn:fail:schema?
            (thunk (validate-json (and '1 '2) 1)))
  (test-exn "and #f #t"
            exn:fail:schema?
            (thunk (validate-json (and '1 '2) 2)))
  (test-exn "and #f #f"
            exn:fail:schema?
            (thunk (validate-json (and '1 '2) 3)))
  (test-equal? "empty and"
               (validate-json (and) 1)
               1)
  ; regression test: schema refs used to not handle failure properly.
  ; failure in the referenced schema would result in an exception, rather than using on-fail.
  (test-equal? "or with schema ref"
               (validate-json (or number string) "hello")
               "hello")
  (test-exn "failing or with schema ref"
            #rx"all cases of 'or' failed"
            (thunk (validate-json (or number string) 'null)))
  (test-equal? "object"
               (validate-json (object [age number] [name string])
                              (hasheq 'age 1 'name "mike" 'extra #t))
               (hasheq 'age 1 'name "mike"))
  (test-exn "object not hasheq"
            exn:fail:schema?
            (thunk (validate-json (object [age number] [name string]) 1)))
  (test-exn "object missing field"
            exn:fail:schema?
            (thunk (validate-json (object [age number] [name string])
                                  (hasheq 'age 1))))
  ; TODO fix this scoping issue. it's because object uses =>, which creates a scope
  #;(test-equal? "bindings escape object schema"
               (validate-json (=> (object [age (bind age number)]) age)
                              (hasheq 'age 21))
               21)
  (test-equal? "listof"
               (validate-json (listof number) '(1 2 3))
               '(1 2 3))
  (test-exn "listof not a list"
            #rx"expected a list"
            (thunk (validate-json (listof number) 1)))
  (test-exn "listof element fails"
            #rx"expected a number"
            (thunk (validate-json (listof number) '(1 #t 3))))
  (test-equal? "listof uses inner results"
               (validate-json (listof (=> (bind x number) (* 2 x)))
                              '(1 2 3))
               '(2 4 6))
  #;(test-equal? "listof exposes inner bindings"
              (validate-json (=> (listof (bind x any)) (list x x))
                             '(1 2 3))
              '((1 2 3) (1 2 3)))
  (test-equal? "listof handles inner failure in an 'or'"
                 (validate-json (or (listof number) any) '(1 #t 2))
                 '(1 #t 2))
  (test-case "recursive  schema"
    (define-schema rose (listof rose))
    (check-equal? (validate-json rose '(() (() ()))) '(() (() ())))
    (check-exn exn:fail:schema? (thunk (validate-json rose '(() () (((1))))))))
  (test-equal? "let schema"
               (validate-json (let ([x (=> number 2)] [y number])
                                (list x y))
                              3)
               '(2 3))
  (test-equal? "let schema refer to previous bindings"
               (validate-json (let ([x (=> number 2)] [y (=> number x)])
                                (list x y))
                              1)
               '(2 2)))
