#lang s-exp rosette

(require "../util/util.rkt")
(require "ip.rkt")

(provide cidr prefix prefix-ip prefix-length symbolic-prefix same-or-longer-prefix?
         prefix-compare simple-modifier? prefix-overlap same-prefix?)

(define (prefix ip length) `(Prefix ,ip ,length))
(define (prefix? c) (and (pair? c) (eq? 'Prefix (first c))))
(define (prefix-ip c) (second c))
(define (prefix-length c) (third c))

(define cidr prefix)

; NOTE: this representation is faster than a vector that only stores the
; significant bits of the prefix.
; NOTE: it's not clear which number representation: symbolic-unary-bounded-nat, 
; symbolic-binary-bounded-nat, or symbolic-interval is better. performance
; meassurements might be in order.
; NOTE: using lists instead of vector for the prefix doesn't seem to impact 
; performance much
(define (symbolic-prefix)
  (prefix (symbolic-ip)
          (symbolic-succ (symbolic-binary-bounded-nat 5))))

(define (prefix-overlap p q)
  (define p* (take (ip-bits (prefix-ip p)) (prefix-length p)))
  (define q* (take (ip-bits (prefix-ip q)) (prefix-length q)))
  (or (list-prefix? p* q*) 
      (list-prefix? q* p*)))

(define (simple-modifier? m)
  (case m [(exact) true] [(longer) true] [(orlonger) true] [else false]))

; longer prefix (vector-length), means we can route a smaller subnet
; http://www.juniper.net/techpubs/en_US/junos14.1/topics/usage-guidelines/policy-configuring-route-lists-for-use-in-routing-policy-match-conditions.html#id-10213710
;
; if a is (cidr (ip 192 168 0 0) 16) 'orlonger then
;   a = 192 168 1 0 / 24
;   reject
; else
;   a = 192   0 0 0 /  8
(define (prefix-compare mode action-prefix route-prefix)
  (define l (prefix-length action-prefix))
   (and
     ((case mode [(exact) =] [(longer) >] [(orlonger) >=])
      (prefix-length route-prefix) l)
    ; action-prefix's length is >= l
    (eq? (take (ip-bits (prefix-ip action-prefix)) l) (take (ip-bits (prefix-ip route-prefix)) l))))

(define (same-or-longer-prefix? p q)
  (prefix-compare 'orlonger p q))

(define (same-prefix? p q)
  (prefix-compare 'exact p q))
