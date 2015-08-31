#lang s-exp rosette

(require rackunit)

(require "../main/util/util.rkt")

(test-case
  "list tests"
  ; NOTE, we have to use check eq? instead of check-eq? to get rosette eq? 
  ; semantics instead of racket semantics for eq?
  (check eq? (list-set (list 1 2 3) 1 3) (list 1 3 3))
  (check eq? (list-set (list 1 2 3) 2 4) (list 1 2 4))

  (check eq? 
    (list-indices (list #f #t #f #t #t #f))
    '(1 3 4))

  (check eq? (map-edges [lambda (a b) (cons a b)] '(A B C)) '((A . B) (B . C)))
  (check eq? (map-edges [lambda (a b) (cons a b)] '(A B)) '((A . B)))
  (check eq? (map-edges [lambda (a b) (cons a b)] '(A)) '())
  (check eq? (map-edges [lambda (a b) (cons a b)] '()) '())

  (check eq? (index '(a b c d) 'a) 0)
  (check eq? (index '(a b c d) 'c) 2)

  (check eq? (listify 'a) '(a))
  (check eq? (listify '()) '())
  (check eq? (listify '(a)) '(a))
  (check eq? (listify '(a b)) '(a b))

  (check-true (list-prefix? '(a b) '(a b c d)))
  (check-true (list-prefix? '(a) '(a b)))
  (check-true (list-prefix? '(a) '(a)))
  (check-true (list-prefix? '() '(a b c d)))
  (check-true (list-prefix? '() '()))
  (check-false (list-prefix? '(a b) '(a)))
  (check-false (list-prefix? '(a b) '()))
  (check-false (list-prefix? '(a) '(b)))
  (check-false (list-prefix? '(a b) '(a c)))
  (check-false (list-prefix? '(a b) '(c b)))
  (check-false (list-prefix? '(a) '()))
)

(test-case
  "symbolic nat tests"
  ; verify* returns false if no counter example can be found
  (define 0..3 (symbolic-interval 0 3))
  (check-false (verify* (assert (and (<= 0 0..3) (<= 0..3 3)))))

  (define 0..4 (symbolic-unary-bounded-nat 4))
  (check-false (verify* (assert (and (<= 0 0..4) (<= 0..4 4)))))

  (define 0..7 (symbolic-binary-bounded-nat 3))
  (check-false (verify* (assert (and (<= 0 0..7) (<= 0..7 7)))))

  (define 0..8 (symbolic-succ (symbolic-binary-bounded-nat 3)))
  (check-false (verify* (assert (and (<= 0 0..8) (<= 0..8 8))))))

(test-case
  "symbolic tests"
  (define-symbolic b boolean?)

  (check-false (symbolic? #f))
  (check-false (symbolic? (+ 1 2)))
  (check-true  (symbolic? b)))

(test-case
  "subset tests"
  (define e0 (subset '(A B C)))
  (check-false (subset-ref e0 'A))
  (check-false (subset-ref e0 'B))
  (check-false (subset-ref e0 'C))
  (define e1 (subset-set e0 'B #t))
  (check-false (subset-ref e1 'A))
  (check-true  (subset-ref e1 'B))
  (check-false (subset-ref e1 'C))
  (define e2 (subset-set e1 'C #t))
  (check-false (subset-ref e2 'A))
  (check-true  (subset-ref e2 'B))
  (check-true  (subset-ref e2 'C)))
