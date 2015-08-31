#lang s-exp rosette

(require (only-in "juniper/translate.rkt" load-as))
(require "network/network.rkt")
(require "config/config.rkt")
(require "util/extraction.rkt")

(provide load-prop load-config)

(define-namespace-anchor a)

(define (load-prop args)
  (current-directory (car args))
  (define ns (namespace-anchor->namespace a))
  (define policy ((parameterize ([current-namespace ns])
    (load "setup.rkt")
    (eval 'policy)) (cdr args)))
  (lambda (r i o p ai al ae) (policy r p al)))

(define (load-config args)
  (current-directory (car args))
  (define ns (namespace-anchor->namespace a))
  ((parameterize ([current-namespace ns])
    (load "setup.rkt")
    (eval 'as)) (cdr args)))
