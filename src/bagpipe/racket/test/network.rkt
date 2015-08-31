#lang s-exp rosette/safe

(require rackunit)

(require "../main/util/util.rkt")
(require "../main/network/network.rkt")

(define (bit-list l) (map (lambda (n) (not (zero? n))) l))

(test-case
  "test number->bits->number"
  (check eq? (number->bits 3 4) (bit-list '(1 0 0)))
  (check eq? (number->bits 2 4) 'error)
  (check eq? (number->bits 8 256) 'error)
  (check eq? (number->bits 8 255) (bit-list '(1 1 1 1 1 1 1 1)))
  (check eq? (number->bits 1 0) (bit-list '(0)))

  (check eq? (bits->number (list #t #f #t #f #t #f #t #f)) 170)
  (check eq? (bits->number (list #t)) 1)
  (check eq? (bits->number (list #f)) 0))

(test-case
  "test ip"
  (check eq? (ip 192 168 1 0) (ip 192 168 1 0))
  (check eq? (ip-bits (ip 64 57 16 1))
    (bit-list '(
      0 1 0 0 0 0 0 0
      0 0 1 1 1 0 0 1
      0 0 0 1 0 0 0 0
      0 0 0 0 0 0 0 1
    ))))

(test-case
  "test environment"
  (define e0 (environment '(A B) '(X Y)))
  (define e1 (environment '(B C) '()))
  (define e2 (environment '(A D) '(Z X)))
  (define e (environment '(A B C D) '(X Y Z)))
  (check eq? (environment-merge (list e0)) e0)
  (check eq? (environment-merge (list e0 e1 e2)) e))

(test-case
  "test announcement"
  (define a0 (default-announcement (cidr (ip 255 168 1 1) 16) (environment '(A B) '(X Y))))
  (define a1 (announcement-community-set a0 'A #t))
  (define a2 (announcement-aspath-set a1 'Y #t))
  (check eq? (announcement-aspath-test a2 'Y) #t)
  (check eq? (announcement-aspath-test a2 'X) #f)
  (check eq? (announcement-community-test a2 'A) #t)
  (check eq? (announcement-community-test a2 'B) #f)
  (check same-prefix? (announcement-prefix a2) (cidr (ip 255 168 124 12) 16)))

(test-case
  "prefix-overlap tests"
  (check-true  (prefix-overlap (cidr (ip 205 213 0 0) 16)
                               (cidr (ip 205 213 0 0) 16)))
  (check-true  (prefix-overlap (cidr (ip 205   0 0 0)  8)
                               (cidr (ip 205 213 0 0) 16)))
  (check-true  (prefix-overlap (cidr (ip 205 213 0 0) 16)
                               (cidr (ip 205   0 0 0)  8)))
  (check-false (prefix-overlap (cidr (ip 205 213 0 0) 16)
                               (cidr (ip 205 214 0 0) 16)))
  (check-false (prefix-overlap (cidr (ip 205 213 0 0) 16)
                               (cidr (ip  10   0 0 0)  8))))
