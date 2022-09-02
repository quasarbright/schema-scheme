#lang racket

(module+ test (require rackunit))
(provide (all-defined-out))

(require bindingspec (for-syntax syntax/parse))

(define-hosted-syntaxes

  (binding-class var #:description "schema-bound variable")
  (binding-class schema-ref
                 #:description "schema reference"
                 #:binding-space schema-scheme)
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
                       #:binding [(nest-one s (host guard)) (nest-one s tail)]
                       ;#:binding [(nest-one s (host guard)) (nest-one s tail)]
                       (object-has-field name:id s:schema)
                       #:binding (nest-one s tail)))

(define-syntax define-schema-scheme-syntax
  (syntax-parser
    [(_ name:id rhs:expr)
     #:with spaced-name ((make-interned-syntax-introducer 'schema-scheme) (attribute name) 'add)
     #'(define-syntax spaced-name rhs)]))

(define-syntax define-schema-syntax
  (syntax-parser
    [(_ (macro-name:id args ...) body ...) #'(define-schema-syntax macro-name (λ (args ...) body ...))]
    [(_ macro-name:id transformer) #'(define-schema-scheme-syntax macro-name (schema-macro transformer))]))

(define-host-interface/expression (validate-json s:schema-top json:expr)
  #:binding [s (host json)]
  #:with s^ (compile-schema #'s)
  #'(s^ json))

(begin-for-syntax
  (define-literal-set schema-literals
    #:datum-literals (list-of list and or bind when quote quasiquote unquote => cons object-has-field any equal?)
    ())

  (define (compile-schema schema)
    #`(λ (json) #,(compile-validate schema #'json #'result #'result #'(λ ([msg "validation failed"]) (error 'validate-json msg)))))
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
          (displayln #'var^)
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
          #`(if (and (hash? json) (hash-has-key? json 'name))
                (let ([field (hash-ref json 'name)])
                  #,(compile-validate #'schema #'field #'result #'body #'on-fail))
                (on-fail (format "expected an object, but got ~a" json)))])]))

  (define (compile-host-expr e)
    (resume-host-expansion e #:reference-compilers ([var compile-reference]))))

(module+ test
  (check-equal? (validate-json any 1) 1)
  (check-equal? (validate-json (object-has-field foo any) (hasheq 'foo 1)) 1)
  (check-equal? (validate-json (=> any 2) 1) 2)
  (check-equal? (validate-json (when any #t) 1) 1)
  (check-equal? (validate-json (bind x any) 1) 1)
  (check-equal? (validate-json (=> (bind y any) (list y)) 1) '(1)))
