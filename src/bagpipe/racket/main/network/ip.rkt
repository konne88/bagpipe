#lang s-exp rosette

(require "../util/util.rkt")

(provide ip ip-bits symbolic-ip number->bits bits->number)


(define (number->bits k n)
  (define (unsafe-number->bits k n)
    (if (zero? k)
      '()
      (append
        (unsafe-number->bits (sub1 k) (quotient n 2))
        (list (not (zero? (remainder n 2)))))))
  (if (or (negative? n) (>= n (expt 2 k)))
    undefined
    (unsafe-number->bits k n)))

(define (bits->number bits)
  (if (null? bits)
    0
    (+ (if (car bits) (expt 2 (sub1 (length bits))) 0)
       (bits->number (cdr bits)))))

(define (ip-repr bits) `(IP-Repr ,bits))
(define (ip-repr? c) (and (pair? c) (eq? 'IP-Repr (first c))))
(define (ip-repr-bits c) (second c))

(define ip-bits ip-repr-bits)

(define (ip a b c d)
  (ip-repr (append (number->bits 8 a) (number->bits 8 b) (number->bits 8 c) (number->bits 8 d))))

(define (symbolic-ip)
  (ip-repr (symbolic-list 32)))
