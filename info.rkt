#lang info
(define collection "schema-scheme")
(define deps '("base" "ee-lib"))
(define build-deps '("scribble-lib" "racket-doc" "rackunit-lib"))
(define scribblings '(("scribblings/schema-scheme.scrbl" ())))
(define pkg-desc "An extensible hosted dsl for creating json schemas")
(define version "0.0")
(define pkg-authors '(mdelmonaco))
