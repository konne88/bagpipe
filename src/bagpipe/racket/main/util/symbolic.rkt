#lang s-exp rosette

(require "list.rkt")

(provide 
  symbolic? 
  symbolic-boolean symbolic-list
  symbolic-interval symbolic-unary-bounded-nat symbolic-binary-bounded-nat symbolic-succ)

(define (symbolic? x)
  (not (eq? (term-name x) #f)))

(define (symbolic-boolean)
  (define-symbolic* b boolean?)
  b)

(define (symbolic-list k)
  (build-list k (lambda (_) (symbolic-boolean))))

; TODO is there a better way to define symbolic intervals?
; return n, such that: start <= n <= end
(define (symbolic-interval start end)
  (define-symbolic* n number?)
  (max start (min end n)))

; return n, such that: 0 <= n <= bound
(define (symbolic-unary-bounded-nat bound)
  (if (zero? bound)
    0
    (begin
      (define-symbolic* b boolean?)
      (if b 
        0 
        (add1 (symbolic-unary-bounded-nat (sub1 bound)))))))

; return n, such that: 0 <= n < 2^bits
(define (symbolic-binary-bounded-nat bits)
  (define-symbolic* b boolean?)
  (if (zero? bits)
    0
    (+ (* (if b 1 0) (expt 2 (sub1 bits))) (symbolic-binary-bounded-nat (sub1 bits)))))

(define (symbolic-succ n)
  (define-symbolic* b boolean?)
  (if b 0 (add1 n)))
