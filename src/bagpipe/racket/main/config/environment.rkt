#lang s-exp rosette/safe

(require "../util/util.rkt")
(require "../network/network.rkt")
(require "denote.rkt")
(require "../config/config.rkt")

(provide (all-defined-out))


(define (collect-communities policies) (remove-duplicates
  (append-map (lambda (policy)
    (append-map (lambda (term)
      (append
        (append-map (lambda (from)
          (cond
            [(community? from) (list (community-community from))]
            [else              '()])
        ) (term-froms term))
        (append-map (lambda (then)
          (cond
            [(community-add?    then) (list (community-add-community    then))]
            [(community-delete? then) (list (community-delete-community then))]
            [else              '()])
        ) (term-thens term))
      )
    ) policy)
  ) policies)))

(define (collect-as-paths policies) (remove-duplicates
  (append-map (lambda (policy)
    (append-map (lambda (term)
      (append
        (append-map (lambda (from)
          (cond
            [(as-path? from) (list (as-path-aspath from))]
            [else            '()])
        ) (term-froms term))
        (append-map (lambda (then)
          (cond
            [else '()])
        ) (term-thens term))
      )
    ) policy)
  ) policies)))

(define (policies->environment ps)
  (define cs (collect-communities ps))
  (define as (collect-as-paths ps))
  (environment cs as))

(define (neighbors->environment ns)
  (environment-merge (map [lambda (n)
    (environment-merge (list
      (policies->environment (neighbor-import n))
      (policies->environment (neighbor-export n))
    ))
  ] ns)))

(define (as->environment as)
  (environment-merge (map [lambda (r)
    (neighbors->environment (router-neighbors r))
  ] (as-routers as))))

