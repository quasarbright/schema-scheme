#lang racket

(require syntax/parse (for-syntax syntax/parse))

(module+ test (require rackunit))

(define-syntax validate
  (syntax-parser
    [(_ schema json)
     #'(let ([json-pv json]) (validate* schema json-pv identity))]))

(define (validate-equal? json expected on-success on-fail)
  (if (equal? json expected)
      (on-success json)
      (on-fail)))

(define (validate-cons json on-success on-fail)
  (if (cons? json)
      (on-success (car json) (cdr json))
      (on-fail)))

#;(-> jsexpr? (-> any/c any/c) (-> (list-of any/c) any) (-> any))
; maps proc over elements
(define (validate-list-of json proc on-success on-fail)
  (if (list? json)
      (on-success (map proc json))
      (on-fail)))

(define-syntax validate*
  (syntax-parser
    ; on-success is a procedure that accepts the result of validation
    ; it is important that the procedure's full syntax is maintained
    ; everything should compile to one huge lambda that ends up referencing things from outer lambdas
    [(_ schema json-pv:id on-success)
     (syntax-parse #'schema
       #:datum-literals (list cons quote number => : when and or ? list-of)
       [(: var:id inner-schema)
        #'(validate* inner-schema json-pv (λ (var) (on-success var)))]
       [(when inner-schema test:expr)
        #'(validate* inner-schema json-pv (λ (result)
                                            (if expr
                                                result
                                                (error 'validate "'when' guard failed ~a ~a" 'test json))))]
       [(=> inner-schema body:expr)
        #'(validate* inner-schema json-pv (λ (ignored)
                                            (on-success body)))]
       [(quote datum)
        #'(let ([qdatum (quote datum)])
            (validate-equal? json-pv qdatum
                             on-success
                             (λ () (error 'validate "expected ~a but got ~a" qdatum json-pv))))]
       [(cons first-schema rest-schema)
        #'(validate-cons json-pv
                         (λ (first-json rest-json)
                           (validate* first-schema first-json
                                      (λ (first-result)
                                        (validate* rest-schema rest-json
                                                   (λ (rest-result)
                                                     (on-success (cons first-result rest-result)))))))
                         (λ () (error 'validate "expected cons ~a" json-pv)))]
       [(list-of element-schema)
        #'(validate-list-of json-pv
                            ; creates a new scope for captured variables
                            (λ (element) (validate element-schema element))
                            on-success
                            (λ () (error 'validate "expected a list ~a" json-pv)))])]))

(module+ test
  (check-equal? (validate (=> (cons (: a '1) (: b '(2))) (list a b)) '(1 2)) '(1 (2)))
  (check-equal? (validate (=> (cons (: a '1) (: a '(2))) a) '(1 2)) '(2))
  (check-equal? (validate (=> (: x (=> (cons (: x '1) (cons (: y '2) '())) (list x y))) (list x y)) '(1 2))
                '((1 2) 2))
  (check-equal? (validate (list-of (=> (cons (: x '1) '()) x)) '((1) (1))) '(1 1)))
