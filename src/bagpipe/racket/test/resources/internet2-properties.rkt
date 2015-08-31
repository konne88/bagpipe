#lang s-exp rosette/safe

(require "../../main/util/util.rkt")
(require "../../main/network/network.rkt")
(require "../../main/config/denote.rkt")
(require "../../main/config/config.rkt")
(require "../../main/juniper/parser.rkt")
(require "../../main/juniper/translate.rkt")

(provide (all-defined-out))

#|
(define sanity-in-count 0)

(define (inc-sanity-in-count!)
  (set! sanity-in-count (+ sanity-in-count 1)) )

(define (neighbor-remove-sanity-in n)
  (neighbor-import-update n [lambda (policies)
    (map [lambda (policy) 
      (filter [lambda (term) 
        (if (eq? term sanity-in)
          (begin
            (inc-sanity-in-count!)
            #f)
          #t)
      ] policy)
    ] policies)
  ]))
|#

(define (indiana-gigapop? n)
  (eq? (neighbor-ip n) (ip 149 165 254 20)))

; ITN = RedCLARA and ANSP
(define atla-itns (list (ip 198 32 252 230) (ip 200 0 207 9)))

(define (atla-itn? n)
  (ormap (curry eq? (neighbor-ip n)) atla-itns))

(define ingp-policies (neighbor-import (neighbor-remove-sanity-in ingp)))

#|
; NOTE we want to verify the following property. Namely: if the annoucement contains 
; the BLOCK-TO-EXTERNAL community, it should not be forwarded (but rejected).
(define (block-to-external? fwd)
  (define a (forwarding-announcement fwd))
  (define r (forwarding-result fwd))
  (implies
    (has-community? 'BLOCK-TO-EXTERNAL a)
    (rejected? r)))

(define order '(
  (PEER     . LOW)     ;  40
  (PEER     . DEFAULT) ; 100
  (CUSTOMER . LOW)     ; 140
  (PEER     . HIGH)    ; 160
  (CUSTOMER . DEFAULT) ; 200
  (CUSTOMER . HIGH)    ; 260
))

(define (value peers neighbor a)
  (index order 
    (if (is-peer? peers neighbor)
      (cons 'PEER 
            (cond 
              [(has-community? 'HIGH-PEERS a) 'HIGH]
              [(has-community? 'LOW-PEERS  a)  'LOW]
              [else                        'DEFAULT]))
      (cons 'CUSTOMER
            (cond 
              [(has-community? 'HIGH a) 'HIGH]
              [(has-community? 'LOW  a)  'LOW]
              [else                  'DEFAULT])))))

(define (compare a b)
  (cond
    [(= a b) '=]
    [(< a b) '<]
    [else    '>]))

(define (preference-matches-community? peers fwd0 fwd1)
  (define src0 (car (forwarding-path-ips fwd0)))
  (define a0 (forwarding-announcement fwd0))
  (define r0 (forwarding-result fwd0))
  (define src1 (car (forwarding-path-ips fwd1)))
  (define a1 (forwarding-announcement fwd1))
  (define r1 (forwarding-result fwd1))
  (eq?
    (compare (value peers src0 a0)
             (value peers src1 a1))
    (compare (announcement-pref (flow-announcement r0))
             (announcement-pref (flow-announcement r1)))))

|#

(define (is-peer? peers neighbor)
  (not (eq? #f (member neighbor peers))))

; we need to parse manually, because after parsing 
; all the policy names have been removed
(define (infer-peers config-files)
  (define (has-import? policy n)
    (member policy (neighbor-import n)))
  (define configs (map juniper->sexp config-files))
  (define ns (append-map translate-neighbors configs))
  (let*-values (
    [(customers ns) (partition (curry has-import? 'SET-PREF     ) ns)]
    [(peers     ns) (partition (curry has-import? 'SET-PREF-PEER) ns)])
    (map neighbor-ip peers)))

(define internet2-peers (list
  (ip 198 32 252 230)
  (ip 200 0 207 9)
  (ip 205 189 32 98)
  (ip 134 75 108 45)
  (ip 211 79 48 177)
  (ip 192 31 99 133)
  (ip 117 103 111 154)
  (ip 64 57 28 70)
  (ip 198 71 46 34)
  (ip 198 71 45 195)
  (ip 192 150 29 5)
  (ip 192 41 213 110)
  (ip 64 57 30 1)
  (ip 143 56 242 33)
  (ip 64 57 20 229)
  (ip 198 71 46 41)
  (ip 200 23 60 121)
  (ip 64 57 28 82)
  (ip 207 231 246 3)
  (ip 198 129 48 1)
  (ip 207 231 240 155)
  (ip 198 32 177 14)
  (ip 64 57 20 193)
  (ip 150 99 199 93)
  (ip 207 231 240 133)
  (ip 207 231 240 136)
  (ip 207 231 240 142)
  (ip 207 231 241 4)
  (ip 207 231 240 149)
  (ip 207 231 242 136)
  (ip 207 231 240 150)
  (ip 207 231 242 152)
  (ip 203 181 248 142)
  (ip 210 25 189 133)
  (ip 207 231 242 146)
  (ip 64 57 28 15)
  (ip 205 189 32 94)
  (ip 205 189 32 118)
  (ip 150 99 200 193)
  (ip 211 79 48 157)
  (ip 64 57 28 66)
  (ip 86 36 105 177)
  (ip 109 105 98 9)
  (ip 150 189 255 129)
  (ip 199 58 120 134)
  (ip 198 71 46 38)
  (ip 198 71 45 237)
  (ip 198 71 45 209)
  (ip 198 71 46 43)
  (ip 198 32 153 3)
  (ip 198 32 153 121)
  (ip 198 71 45 239)
  (ip 207 231 245 131)
  (ip 207 231 240 13)
  (ip 207 231 240 23)
  (ip 64 57 20 189)
  (ip 207 231 240 4)
  (ip 207 231 240 10)
  (ip 207 231 241 136)
  (ip 207 231 240 2)
  (ip 207 231 240 6)
  (ip 207 231 241 149)
  (ip 207 231 240 21)
  (ip 207 231 240 22)
  (ip 64 57 20 233)
  (ip 192 84 8 253)
  (ip 198 124 194 9)
  (ip 198 71 46 149)
  (ip 62 40 125 17)
  (ip 64 57 28 62)
  (ip 150 99 199 189)
  (ip 198 71 45 211)
))
