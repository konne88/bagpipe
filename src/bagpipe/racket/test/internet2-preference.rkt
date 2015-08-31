#lang s-exp rosette

(current-bitwidth 10)

(require rackunit)
(require rosette/lib/meta/meta)
(require rosette/solver/smt/z3)

(current-solver (new z3%))

(require "../main/util/util.rkt")
(require "../main/network/network.rkt")
(require "../main/juniper/parser.rkt")
(require "../main/juniper/denote.rkt")
(require "../main/juniper/translate.rkt")
(require "../main/juniper/as.rkt")
(require "../main/juniper/environment.rkt")
(require "resources/internet2-properties.rkt")

; NOTE preference verification
; we have to forward announcements through an AS with exactly one router.
; 
;                   ________________________
;                  / AS under consideration \  preference?
;                 /                          \     |
; [source/src] --{-------> [router/rtr] ------}----|---> [sink/dst]
;                 \                          /     |
;                  \________________________/
;
; An announcement comes into existence at [source],
; is then received by [router] (in the AS under consideration), 
; and finally sent to [sink].

"======[ LOADING ]======="

(define peers (list
  (ip 64 57 28 82)
))

(define pop "kans")
(define config-file (bagpipe-path (string-append "configs/internet2/" pop ".conf")))

(define as (load-as (list config-file)))
(define env (as->environment as))
(define rtr (first (as-routers as)))
(define rtr-ip (router-ip rtr))
(define neighbors (take (external-neighbor-ips rtr) 3))

(displayln neighbors)
(flush-output)


"======[ TESTING ]========"
(flush-output)

(test-case
  "test is-peer?"
  (check-true  (is-peer? peers (ip 64 57 28 82)))
  (check-false (is-peer? peers (ip 0 57 28 82))))

(define (denote-trace-result path-ips a)
    (forwarding-result (denote-trace as (trace path-ips a))))

(test-case
  "internet2 tests"

  ; WiscREN client of kansas
  (define src0 (ip 205 213 119 25))
   ; CUDI peer of kansas
  (define src1 (ip 64 57 28 82))
  ; KanREN client of kansas
  (define dst (ip 64 57 28 178))

  (define src0-rtr-src0 (list src0 rtr-ip src0))
  (define src0-rtr-dst (list src0 rtr-ip dst))
  (define src1-rtr-dst (list src1 rtr-ip dst))

  (define a0 (default-announcement (cidr (ip 74 115 8 0) 24) env))
  (define a0-LOW (announcement-community-set a0 'LOW #t))
  (define a1 (default-announcement (cidr (ip 74 115 8 0) 25) env))
 
  (define no-peers '())

  (check eq? (value peers src0 a0) (value peers src0 a0))
  (check eq? (value peers src0 a0-LOW) (value peers src0 a0-LOW))
  (check-true (< (value peers src0 a0-LOW) (value peers src0 a0)))
  (check-true (> (value peers src0 a0) (value peers src0 a0-LOW)))

  (check-pred accepted? (denote-trace-result src0-rtr-src0 a0))

  (check-true (competing-announcements?
    (denote-trace as (trace src0-rtr-src0 a0-LOW))
    (denote-trace as (trace src0-rtr-src0 a0-LOW))))

  (check-true (preference-matches-community? peers
    (denote-trace as (trace src0-rtr-src0 a0-LOW))
    (denote-trace as (trace src0-rtr-src0 a0-LOW))))

  (check-true (preference-matches-community? peers
    (denote-trace as (trace src0-rtr-src0 a0-LOW))
    (denote-trace as (trace src0-rtr-src0 a0))))

  (check-true (valid-preferences? (curry preference-matches-community? peers)
    (denote-trace as (trace src0-rtr-src0 a0))
    (denote-trace as (trace src0-rtr-src0 a0))))

  (check-pred accepted? (denote-trace-result src1-rtr-dst a1))

  (check-true (competing-announcements?
    (denote-trace as (trace src0-rtr-dst a0))
    (denote-trace as (trace src1-rtr-dst a1))))

  (check-false (preference-matches-community? no-peers
    (denote-trace as (trace src0-rtr-dst a0))
    (denote-trace as (trace src1-rtr-dst a1))))

  (define t  (trace src0-rtr-src0 (symbolic-announcement env)))
  (define t* (trace src0-rtr-src0 (symbolic-announcement env)))

  (check-pred correct? (verify-preference (curry preference-matches-community? peers) as t t*))

  (define t0 (trace src0-rtr-dst (symbolic-announcement env)))
  (define t1 (trace src1-rtr-dst (symbolic-announcement env)))

  (check-pred list?
    (verify-preference (curry preference-matches-community? no-peers) as t0 t1))

  (check-pred correct?
    (verify-preference (curry preference-matches-community? peers) as t0 t1))
)

"======[ INDIVIDUAL VERIFICATION ]======="
(flush-output)

(for-each [lambda (dst)
  (for-each [lambda (src0)
    (for-each [lambda (src1)
      (define trace0 (trace (list src0 rtr-ip dst) (symbolic-announcement env)))
      (define trace1 (trace (list src1 rtr-ip dst) (symbolic-announcement env)))

      (write-string "{")
      (write src0)
      (write-string ", ")
      (write src1)
      (write-string "} -> ")
      (write dst)
      (write-string ": ")
      (flush-output)
      ; NOTE with the test-cases enabled, this is surprisingly slow, given that the 
      ; exact same query is much faster in tests above
      (write (verify-preference (curry preference-matches-community? internet2-peers) as trace0 trace1))
      (write-string "\n")
      (flush-output)
    ] neighbors)
  ] neighbors)
] neighbors)
