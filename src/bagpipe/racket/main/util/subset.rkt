#lang s-exp rosette/safe

(require "symbolic.rkt")
(require "list.rkt")

(provide subset subset-ref subset-set symbolic-subset subset-empty subset->list)


(define (lookup e x)
  (index (subset-repr-map e) x))

(define (subset-ref e x)
  (define i (lookup e x))
  (list-ref (subset-repr-bits e) i))

(define (subset-set e x b)
  (define i (lookup e x))
  (subset-repr 
    (list-set (subset-repr-bits e) i b) 
    (subset-repr-map e)))

(define (subset->list e)
  (define is (list-indices (subset-repr-bits e)))
  (define (unmap i) (list-ref (subset-repr-map e) i))
  (map unmap is))

(define (subset-repr bits map) `(Subset-Repr ,bits ,map))
(define (subset-repr? c) (eq? 'Subset-Repr (first c)))
(define (subset-repr-bits c) (second c))
(define (subset-repr-map c) (third c))

(define (subset m)
  (subset-repr (build-list (length m) (lambda (_) #f)) m))

(define (subset-empty e)
  (subset (subset-repr-map e)))

(define (symbolic-subset m)
  (subset-repr (symbolic-list (length m)) m))
