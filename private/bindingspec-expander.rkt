#lang racket

(module+ test (require rackunit))
(provide (all-defined-out)
         (for-space schema-scheme (all-defined-out)))

(require bindingspec (for-syntax syntax/parse))

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
                       any
                       #:binding {tail}
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
                       #:binding [(nest-one s1 []) (nest-one s2 [])]))

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
; TODO create fail schema and make that the base case for (or)
(define-schema-syntax or (syntax-rules ()
                           [(or schema) schema]
                           [(or schema0 schema ...) (or2 schema0 (or schema ...))]))

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

(define-host-interface/expression (validate-json s:schema-top json:expr)
  #:binding [s (host json)]
  #:with s^ (compile-schema #'s)
  #'(s^ json))

(begin-for-syntax
  (define-literal-set schema-literals
    #:datum-literals (list-of list and or2 bind when quote quasiquote unquote => cons object-has-field any equal? ?)
    ())

  (define (compile-schema schema)
    #`(λ (json) #,(compile-validate schema #'json #'result #'result #'(λ ([msg "validation failed"]) (fail-validation msg)))))
  ; on-fail is syntax for a (-> [string?] any) which takes in an optional error message and, if there are no other schemas to try, errors out.
  ; 'json' and 'result' must be identifiers.
  ; the output is syntax that validates 'json' against 'schema' and binds the result of validating to 'result' in 'body',
  ; or calls 'on-fail' with an error message.
  (define (compile-validate schema json result body on-fail)
    (syntax-parse (list schema json result body on-fail)
      [(schema json:id result:id body on-fail)
       (syntax-parse #'schema
         #:literal-sets (schema-literals)
         [(bind var:id schema)
          #:with var^ (compile-binder! #'var)
          (compile-validate #'schema #'json #'result #'(let ([var^ result]) body) #'on-fail)]
         [(when schema guard)
          (compile-validate #'schema
                            #'json
                            #'result
                            #`(if #,(compile-host-expr #'guard) body (on-fail "'when' guard evaluated to #f"))
                            #'on-fail)]
         [(=> schema action)
          (compile-validate #'schema
                            #'json
                            #'ignored
                            #`(let ([result #,(compile-host-expr #'action)]) body)
                            #'on-fail)]
         [any #'(let ([result json]) body)]
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
                  #,(compile-validate #'car-schema
                                      #'car-value
                                      #'car-result
                                      (compile-validate #'cdr-schema
                                                        #'cdr-value
                                                        #'cdr-result
                                                        #'(let ([result (cons car-result cdr-result)])
                                                            body)
                                                        #'on-fail)
                                      #'on-fail))
                (on-fail (format "expected a cons, but got ~v " json)))]
         ; TODO 'any' should be written in terms of this
         [(? valid? desc)
          #`(if (#,(compile-host-expr #'valid?) json)
                (let ([result json]) body)
                (on-fail (format "expected ~a, but got ~v" #,(compile-host-expr #'desc) json)))]
         [schema-ref:id
          ; TODO handle failure, might want to have schemas take in an on-fail continuation or something.
          #`(let ([result (#,(compile-reference #'schema-ref) json)]) body)]
         [(or2 schema1 schema2)
          ; 'body' shouldn't have access to anything bound in 'or'
          #`(let ([body-proc (λ (result) body)])
              #,(compile-validate #'schema1 #'json #'result #'(body-proc result)
                                  #`(λ _ #,(compile-validate #'schema2
                                                             #'json
                                                             #'result
                                                             #'(body-proc result)
                                                             #'on-fail))))])]))

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
            (thunk (validate-json (or '1 '2) 3))))
