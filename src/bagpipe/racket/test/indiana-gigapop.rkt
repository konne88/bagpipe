#lang s-exp rosette/safe

(current-bitwidth 10)

(require rackunit)
(require "../main/util/util.rkt")
(require "../main/network/network.rkt")
(require "../main/config/denote.rkt")
(require "../main/config/config.rkt")
(require "resources/indiana-gigapop.rkt")
(require "resources/internet2-properties.rkt")

(define ingp-policies (neighbor-import (neighbor-remove-sanity-in ingp)))

(define env (environment (map car ingp-communities) (map car ingp-aspaths)))

(define (sane? a) 
  (simple-no-martians? a (denote-policies ingp-policies a)))

(define (process a) (denote-policies ingp-policies a))

(define (pref= p c)
  (= p (announcement-pref (flow-announcement c))))

(test-case
  "test indiana-gigapop denotation"
  (check-true (not (eq? ingp-policies (neighbor-import ingp))))

  (define bad-prefix  (default-announcement (cidr (ip   0   0   0   0)  0) env))
  (define good-prefix (default-announcement (cidr (ip  65 254  96  23) 27) env))
  (define infinera-community (announcement-community-set bad-prefix 'INTERNET2-INFINERA true))
  (define commercial-aspaths (announcement-aspath-set good-prefix 'COMMERCIAL true))
  (define high-community (announcement-community-set good-prefix 'HIGH true))

  (check-pred accepted? (process good-prefix))
  (check-pred rejected? (process bad-prefix))
  (check-pred accepted? (process infinera-community))
  (check-pred rejected? (process commercial-aspaths))

  (check-true (pref= 200 (process good-prefix)))
  (check-true (pref= 260 (process high-community)))

  (check-true (announcement-community-test infinera-community 'INTERNET2-INFINERA))

  (check-pred sane? good-prefix)
  (check-pred sane? bad-prefix)
  (check-false (sane? infinera-community)))
