#lang s-exp rosette

(current-bitwidth 10)

(require rackunit)
(require rosette/lib/meta/meta)

(require "../main/util/util.rkt")
(require "../main/network/network.rkt")
(require "../main/juniper/parser.rkt")
(require "../main/juniper/denote.rkt")
(require "../main/juniper/translate.rkt")
(require "../main/juniper/environment.rkt")
(require "../main/juniper/as.rkt")
(require "resources/internet2-properties.rkt")
(require "resources/indiana-gigapop.rkt")

; NOTE internet2 importing
; to verify a property about the import of annoucements, 
; we have to verify the import forall annoucements from all sources.
;
;                   _______________________
;         import?  / AS under consideration  
;            |    /                
; [source] --|---{--> [receiver] 
;            |    \                    
;                  \_______________________
;
; An annoucement comes into existence at [source],
; and is then received by [receiver] (in the AS under consideration)


(define as (load-as (list (bagpipe-path "configs/internet2/atla.conf"))))
(define env (as->environment as))
(define atla (first (as-routers as)))
(define atla-ip (router-ip atla))

"======[ VERIFICATION ]======="
(flush-output)

(time
  (define a (symbolic-announcement env))
  (for-each [lambda (src-ip)
    (define path (list src-ip atla-ip))
    (write path)
    (write-string ": ")
    (flush-output)
    (write
      (verify-trace no-martians? as (trace path a)))
    (write-string "\n")
    (flush-output)
  ] (external-neighbor-ips atla))
)
