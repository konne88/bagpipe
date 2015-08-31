#lang s-exp rosette/safe

(require "../network/network.rkt")
(require "../util/util.rkt")
(require "../config/config.rkt")

(require rosette/lib/meta/meta)

(provide (all-defined-out))

(define (flow ctrl announcement) `(Flow ,ctrl ,announcement))
(define (flow? c) (and (pair? c) (eq? 'Flow (first c))))
(define (flow-ctrl c) (second c))
(define (flow-announcement c) (third c))
(define (accepted? c) (eq? 'accept (flow-ctrl c)))
(define (rejected? c) (eq? 'reject (flow-ctrl c)))

; http://www.juniper.net/documentation/en_US/junos13.2/topics/usage-guidelines/policy-configuring-prefix-lists-for-use-in-routing-policy-match-conditions.html
(define (denote-prefix-list-filter from a)
  (define prefix (announcement-prefix a))
  (define m (prefix-list-filter-modifier from))
  (define lst (prefix-list-filter-list from))
  (ormap (lambda (p) (prefix-compare m p prefix)) lst))

; http://www.juniper.net/documentation/en_US/junos13.2/topics/example/policy-prefix-list.html
(define (denote-prefix-list from a)
  (define prefix (announcement-prefix a))
  (define lst (prefix-list-list from))
  (ormap (lambda (p) (prefix-compare 'exact p prefix)) lst))

(define (denote-prefix-lists lists a)
  (ormap (lambda (l) (denote-prefix-list l a)) lists))

; http://www.juniper.net/documentation/en_US/junos12.3/topics/usage-guidelines/policy-configuring-route-lists-for-use-in-routing-policy-match-conditions.html 
; returns #f if the from failed, or a list of thens to take
(define (denote-route-filter from a)
  (define prefix (announcement-prefix a))
  (define m (route-filter-modifier from))
  (define p (route-filter-prefix from))
  (and
    (cond
      ; filter large prefixes, i.e. small subnets
      [(upto? m) (and (<= (prefix-length prefix) (upto-bits m))
                      (prefix-compare 'orlonger p prefix))]
      [(prefix-length-range? m) (and
                                 (<= (prefix-length-range-bits1 m) (prefix-length prefix))
                                 (<= (prefix-length prefix) (prefix-length-range-bits2 m))
                                 (prefix-compare 'orlonger p prefix))]
      [(simple-modifier? m) (prefix-compare m p prefix)]
      [else undefined])
    (route-filter-action from)))

(define (denote-match-condition from a)
  (cond
    [(as-path? from) (announcement-aspath-test a (as-path-aspath from))]
    [(community? from) (announcement-community-test a (community-community from))]
    [(prefix-list-filter? from) (denote-prefix-list-filter from a)]
    [else undefined]))

; returns #f if the from failed, or a list of thens to take
(define (denote-route-filters filters a)
  (let* ([filters (sort filters > #:key [lambda (f) (prefix-length (route-filter-prefix f))])]
         [longest-matching-filter (findf [lambda (f) 
              (prefix-compare 'orlonger (route-filter-prefix f) (announcement-prefix a))
            ] filters)])
    (and longest-matching-filter
         (denote-route-filter longest-matching-filter a))))

(define (denote-match-conditions froms a)
  (and (not (empty? froms))
       (andmap (lambda (from) (denote-match-condition from a)) froms)))

(define (true->null b)
  (if (eq? #t b) '() b))

; returns #f if the from failed, or a list of thens to take
; http://www.juniper.net/documentation/en_US/junos12.2/topics/reference/configuration-statement/policy-statement-edit-policy-options.html
; http://www.juniper.net/techpubs/en_US/junos14.1/topics/usage-guidelines/policy-configuring-route-lists-for-use-in-routing-policy-match-conditions.html#id-10270525
(define (denote-froms froms a)
  (let*-values (
    [(route-filters froms*)           (partition route-filter? froms)]
    [(prefix-lists match-conditions)  (partition prefix-list?  froms*)])
    (true->null
      (or (empty? froms)
          (denote-route-filters route-filters a)
          (denote-prefix-lists prefix-lists a)
          (denote-match-conditions match-conditions a)))))

; returns a modified announcement and flowctrl
(define (denote-then then a)
  (cond
    [(local-preference? then) (flow 'next-then (announcement-pref-set a (local-preference-pref then)))]
    [(community-delete? then) (flow 'next-then (announcement-community-set a (community-delete-community then) false))]
    [(community-add? then)    (flow 'next-then (announcement-community-set a (community-add-community then) true))]
    [(accept? then)        (flow 'accept   a)]
    [(reject? then)        (flow 'reject   a)]
    [(next-term? then)     (flow 'next-term a)]
    [(next-policy? then)   (flow 'next-policy a)]
    [else undefined]))

(define (denote-actions denote-action default continue actions a)
  ; NOTE this is Emina wizzardry that makes BLOCK-TO-EXTERNAL verification much
  ; faster. By default, Rosette's representation of symbolic lists is fast for
  ; peeling (car) elements from the front. for/all changes the representation so
  ; that Rosette is faster iterating over them.
  (for/all ([actions actions])
    (if (null? actions)
      (flow default a)
      (let ([f (denote-action (car actions) a)])
        (if (eq? (flow-ctrl f) continue)
          (denote-actions denote-action default continue (cdr actions) (flow-announcement f))
          f)))))

; returns a modified annoucement, and flowctrl - {continue}
(define (denote-thens thens a)
  (denote-actions denote-then 'next-term 'next-then thens a))

(define (denote-term term a)
  (define from-thens (denote-froms (term-froms term) a))
  (if from-thens
    (denote-thens (if (empty? from-thens) (term-thens term) from-thens) a)
    (flow 'next-term a)))

; http://www.juniper.net/techpubs/en_US/junos14.1/topics/reference/configuration-statement/policy-statement-edit-policy-options.html
; returns a modified annoucement, and flowctrl - {continue, next-term}
(define (denote-policy terms a)  ; terms
  (denote-actions denote-term 'next-policy 'next-term terms a))

; returns a modified annoucement, and flowctrl - {continue, next-term, next-policy}
(define (denote-policies policies a)
  (denote-actions denote-policy 'accept 'next-policy policies a))
