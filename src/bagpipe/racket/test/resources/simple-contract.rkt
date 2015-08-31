#lang s-exp rosette/safe

(require "../../main/util/util.rkt")
(require "../../main/network/network.rkt")
(require "../../main/config/denote.rkt")
(require "../../main/config/config.rkt")

(provide simple-contract profitable? makes-profit?)

(define (has-community? c a)
  (announcement-community-test a c))

(define (routes-subnet-of? prefix a)
  (prefix-compare 'orlonger prefix (announcement-prefix a)))

(define (makes-profit? contract policies a)
  (eq?
    (accepted? (denote-policies policies a))
    (>= (contract a) 0)))

(define (profitable? contract config a)
  (makes-profit? contract (neighbor-import (first (router-neighbors config))) a))

(define private-subnet (cidr (ip 192 168 0 0) 16))

; NOTE a contract will need to contain hundreds of lines of code to only accept
; routes that we actually think the neighboring AS has. We can avoid having to
; write them down by downloading them from a prefix-database.
(define (simple-contract a)
  (cond
    [(routes-subnet-of? private-subnet a) -5]
    [(has-community?    'DISCARD       a) -4]
    [(has-community?    'LOW           a)  2]
    [else 3]))

