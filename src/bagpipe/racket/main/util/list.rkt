#lang s-exp rosette

(require "correctness.rkt")

(provide index list-prefix? build-list listify map-edges list-set list-indices list-remove)


; TODO, this diverges with a symbolic number for n 
; (even though number? is represented finitely in rosette)
(define (build-list n f)
  (letrec 
    ([R (lambda (k)
      (if (= n k)
        '()
        (cons (f k) (R (add1 k))))
    )]) (R 0)))

(define (index l c)
  (if (null? l)
    undefined
    (if (eq? c (car l))
      0
      (add1 (index (cdr l) c)))))

(define (list-prefix? p l)
  (if (null? p)
    #t
    (if (null? l)
      #f
      (and (eq? (car p) (car l))
           (list-prefix? (cdr p) (cdr l))))))

(define (listify v)
  (if (list? v) v (list v)))

(define (map-edges f l)
  (define (rec e l)
    (if (null? l) 
      '()
      (cons (f e (car l)) (rec (car l) (cdr l)))))
  (if (null? l) 
    '()
    (rec (car l) (cdr l))))

(define (list-indices l)
  (define (rec l i)
    (if (null? l)
      '()
      (if (car l)
        (cons i (rec (cdr l) (add1 i)))
        (rec (cdr l) (add1 i)))))
  (rec l 0))

(define (list-set l i b) 
  (append (take l i) (list b) (drop l (add1 i))))

(define (list-remove l i) 
  (append (take l i) (drop l (add1 i))))
