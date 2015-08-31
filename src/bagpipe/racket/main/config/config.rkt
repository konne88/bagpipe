#lang s-exp rosette

(current-bitwidth 10)

(require "../util/util.rkt")
(require "../network/network.rkt")

(provide (all-defined-out))

; AS := [ROUTER]
; ROUTER := IP * [NEIGHBOR]
; NEIGHBOR := IP * TYPE * RULE * RULE
; TYPE := internal + external
; RULE := [POLICY]
; POLICY := [TERM]
; TERM := [FROM] * [THEN]
; FROM := COMMUNITY + AS-PATH + ROUTE-FILTER + PREFIX-LIST + PREFIX-LIST-FILTER
; ROUTER-FILTER := PREFIX * MODIFIER * THEN
; PREFIX-LIST := [PREFIX]
; PREFIX-LIST-FILTER := [PREFIX] * MODIFIER
; MODIFIER := UPTO + PREFIX-LENGTH-RANGE + exact + longer + orlonger
; THEN := COMMUNITY-DELETE + COMMUNITY-ADD + LOCAL-PREF +
;         accept + reject + next-term + next-policy

(define (as routers) `(AS ,routers))
(define (as? c) (and (pair? c) (and (pair? c) (eq? 'AS (first c)))))
(define (as-routers c) (second c))
(define (as-routers-update f as*) (as (f (as-routers as*))))
(define (as-routers-lookup as ip) (findf [lambda (r) (eq? ip (router-ip r))] (as-routers as)))

(define (router ip neighbors) `(Router ,ip ,neighbors))
(define (router? r) (and (pair? r) (eq? 'Router (first r))))
(define (router-ip r) (second r))
(define (router-neighbors r) (third r))
(define (router-neighbors-update f r) (router (router-ip r) (f (router-neighbors r))))
(define (router-neighbors-lookup r ip) (findf [lambda (n) (eq? ip (neighbor-ip n))] (router-neighbors r)))

(define (neighbor ip type import export) `(Neighbor ,ip ,type ,import ,export))
(define (neighbor? n) (and (pair? n) (eq? 'Neighbor (first n))))
(define (neighbor-ip n) (second n))
(define (neighbor-type n) (third n))
(define (neighbor-import n) (fourth n))
(define (neighbor-export n) (fifth n))
(define (neighbor-ip-set n ip)       (neighbor ip              (neighbor-type n) (neighbor-import n)     (neighbor-export n)))
(define (neighbor-type-set n type)   (neighbor (neighbor-ip n) type              (neighbor-import n)     (neighbor-export n)))
(define (neighbor-import-update n f) (neighbor (neighbor-ip n) (neighbor-type n) (f (neighbor-import n)) (neighbor-export n)))
(define (neighbor-export-update n f) (neighbor (neighbor-ip n) (neighbor-type n) (neighbor-import n)     (f (neighbor-export n))))
(define (neighbor-external? n) (eq? 'external (neighbor-type n)))
(define (neighbor-internal? n) (eq? 'internal (neighbor-type n)))

(define (term froms thens) `(Term ,froms ,thens))
(define (term? c) (and (pair? c) (eq? 'Term (first c))))
(define (term-froms c) (second c))
(define (term-thens c) (third c))

; froms
(define (community community) `(Community ,community))
(define (community? c) (and (pair? c) (eq? 'Community (first c))))
(define (community-community c) (second c))

(define (as-path aspath) `(AS-Path ,aspath))
(define (as-path? c) (and (pair? c) (eq? 'AS-Path (first c))))
(define (as-path-aspath c) (second c))

(define (route-filter prefix modifier action) `(Router-Filter ,prefix ,modifier ,action))
(define (route-filter? c) (and (pair? c) (eq? 'Router-Filter (first c))))
(define (route-filter-prefix c) (second c))
(define (route-filter-modifier c) (third c))
(define (route-filter-action c) (fourth c))

(define (prefix-list list) `(Prefix-List ,list))
(define (prefix-list? c) (and (pair? c) (eq? 'Prefix-List (first c))))
(define (prefix-list-list c) (second c))

(define (prefix-list-filter list modifier) `(Prefix-List-Filter ,list ,modifier))
(define (prefix-list-filter? c) (and (pair? c) (eq? 'Prefix-List-Filter (first c))))
(define (prefix-list-filter-list c) (second c))
(define (prefix-list-filter-modifier c) (third c))

; thens
(define (community-delete community) `(Community-Delete ,community))
(define (community-delete? c) (and (pair? c) (eq? 'Community-Delete (first c))))
(define (community-delete-community c) (second c))

(define (community-add community) `(Community-Add ,community))
(define (community-add? c) (and (pair? c) (eq? 'Community-Add (first c))))
(define (community-add-community c) (second c))

(define (local-preference pref) `(Local-Preference ,pref))
(define (local-preference? c) (and (pair? c) (eq? 'Local-Preference (first c))))
(define (local-preference-pref c) (second c))

(define (accept) `(Accept))
(define (accept? c) (and (pair? c) (eq? 'Accept (first c))))

(define (reject) `(Reject))
(define (reject? c) (and (pair? c) (eq? 'Reject (first c))))

(define (next-term) `(Next-Term))
(define (next-term? c) (and (pair? c) (eq? 'Next-Term (first c))))

(define (next-policy) `(Next-Policy))
(define (next-policy? c) (and (pair? c) (eq? 'Next-Policy (first c))))

; prefix compare modifiers, also: 'exact, 'longer, and 'orlonger
(define (upto bits) `(Upto ,bits))
(define (upto? c) (and (pair? c) (eq? 'Upto (first c))))
(define (upto-bits c) (second c))

(define (prefix-length-range bits1 bits2) `(Prefix-Length-Range ,bits1 ,bits2))
(define (prefix-length-range? c) (and (pair? c) (eq? 'Prefix-Length-Range (first c))))
(define (prefix-length-range-bits1 c) (second c))
(define (prefix-length-range-bits2 c) (third c))
