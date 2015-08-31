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

; NOTE internet2 exporting
; to verify a property about the export of annoucements, 
; we have to verify the export forall annoucements from all sources
; to all sinks.
;
;               _________________________
;              / AS under consideration  \  exported?
;             /                           \    |
; [source] --{--> [receiver] -> [sender] --}---|---> [sink]
;             \                           /    |
;              \_________________________/
;
; An annoucement comes into existence at [source],
; is then received by [receiver] (in the AS under consideration),
; is then forwarded to [sender],
; and finally sent to [sink].

"======[ LOADING ]======="

; (define pops '("atla" "chic" "clev" "hous" "kans" "losa" "newy32aoa" "salt" "seat" "wash"))
(define pops '("kans" "salt"))
(define config-files (map [lambda (pop) (bagpipe-path (string-append "configs/internet2/" pop ".conf"))] pops))
(define as (load-as config-files))
(define env (as->environment as))

(define external-sessions 
  (append-map [lambda (router-internal)
    (map [lambda (ip-external)
      (list (router-ip router-internal) ip-external)
      ; change the number to change the number of verified neighbors per router.
      ; 3 is the higest number that terminates quickly.
    ] (take (external-neighbor-ips router-internal) 3))
  ] (as-routers as)))

(displayln external-sessions)


"======[ TESTING ]========"
(flush-output)

(test-case
  "internet2 tests"
  (define path-ips (list
    (ip 64 57 28 245)   ; internet2 router in kansas
    (ip 205 213 119 25) ; WiscREN client of kansas
  ))

  (define a (default-announcement (cidr (ip 0 0 0 0) 0) env))
  (check-true (block-to-external? (denote-trace as (trace path-ips a))))

  (define sa (symbolic-announcement env))

  ; export blocks BLOCK-TO-EXTERNAL
  (check-pred correct? 
    (verify-trace block-to-external? as (trace path-ips sa)))

  ; import does not block BLOCK-TO-EXTERNAL
  (check-pred (curry has-community? 'BLOCK-TO-EXTERNAL)
    (verify-trace block-to-external? as (trace (reverse path-ips) sa)))
)


; How can we prove that an export property is true?
; ---------------------------------------------------------------
; 1) Individually verify the property for every combination of sources, 
;    receivers, senders, and sinks. This performs exactly as expected.
; 2) Implement the semantics of forwarding and perform it with symbolic
;    values for the source ip, and sink ip. This is extreamly slow.
;    2 routers with 2 neighbors takes 25min (only a couple of seconds with
;    appraoch 1)). The reason for this bad performance is most likely that 
;    the lookup of appropriate policies for an ip is complex. After adding
;    some Emina wizzardry (look for NOTE in denote.rkt), the 2 router/2 neighbor
;    verification is instant, and appears to be faster than separate smt 
;    queries even for more neighbors and routers.

"======[ INDIVIDUAL VERIFICATION ]======="  ; Approach 1)
(flush-output)

; NOTE on Konstantin's laptop, for 2 internal routers, with 5 external neighbors each, 
; verification takes 37.445s in total, there are 100 properties checked, thus each 
; takes on average 0.37s.
(time
  (define a (symbolic-announcement env))
  (for-each [lambda (receiver-src)
    (for-each [lambda (sender-dst)
      (define path (append (reverse receiver-src) sender-dst))
      (write path)
      (write-string ": ")
      (flush-output)
      (write
        (verify-trace block-to-external? as (trace path a)))
      (write-string "\n")
      (flush-output)
    ] external-sessions)
  ] external-sessions)
)

"======[ COMBINED VERIFICATION ]======="  ; Approach 2)
(flush-output)

; NOTE on Konstantin's laptop, for 2 internal routers, with 5 external neighbors each, 
; verification takes 113.651s in total, there is only 1 property checked.
(time
  (define a (symbolic-announcement env))
  (define receiver-src (enum-value (symbolic-enum external-sessions)))
  (define sender-dst (enum-value (symbolic-enum external-sessions)))
  (define path (append (reverse receiver-src) sender-dst))
  (write (verify-trace block-to-external? as (trace path a)))
  (write-string "\n")
  (flush-output)
)

"======[ FUSED VERIFICATION ]======="     ; Approach 1 + 2)
(flush-output)

; NOTE on Konstantin's laptop, for 2 internal routers, with 5 external neighbors each, 
; verification takes 851.855s in total, there are 10 properties checked, thus each
; takes on average 85.185s.
(time
  (define a (symbolic-announcement env))
  (define receiver-src (enum-value (symbolic-enum external-sessions)))
  (for-each [lambda (sender-dst)
    (define path (append (reverse receiver-src) sender-dst))
    (write sender-dst)
    (write-string ": ")
    (flush-output)
    (write
      (verify-trace block-to-external? as (trace path a)))
    (write-string "\n")
    (flush-output)
  ] external-sessions)
)
