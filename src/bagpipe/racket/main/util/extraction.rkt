#lang s-exp rosette

(require "../config/denote.rkt")
(require "../config/config.rkt")

(provide lambdas @ match
         denote-neighbors denote-internals available?)

(define-syntax lambdas
  (syntax-rules ()
    [(lambdas (a) es ...) (lambda (a) es ...)]
    [(lambdas (a as ...) es ...) (lambda (a) (lambdas (as ...) es ...))]))

(define-syntax @
  (syntax-rules ()
    [(@ e) e]
    [(@ f a as ...) (@ (f a) as ...)]))

(define-syntax match
  (syntax-rules ()
    [(match e) void]
    [(match e ((t as ...) f) cs ...)
      (if (eq? 't (car e)) 
        (apply (lambda (as ...) f) (cdr e))
        (match e cs ...))]))

(define (coqify-list l)
  (if (null? l)
    `(Nil)
    `(Cons ,(car l) ,(coqify-list (cdr l)))))

(define denote-neighbors (lambdas (as r)
  (define r* (as-routers-lookup as r))
  (coqify-list (map neighbor-ip (filter neighbor-external? (router-neighbors r*))))))

; TODO figure out why I cannot move this function into the header
(define denote-internals (lambdas (as) 
  (coqify-list (map router-ip (as-routers as)))))

(define (available? a)
  (match a
    ((Available _) true)
    ((NotAvailable) false)))

