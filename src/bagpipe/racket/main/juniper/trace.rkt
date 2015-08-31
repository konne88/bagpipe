#lang s-exp rosette

(provide trace-missing-bgp    trace-missing-bgp-enable!
         trace-missing-policy trace-missing-policy-enable!
         supported-cmds       supported-cmds-append)

(define trace-missing-bgp? #f)
(define trace-missing-policy? #f)
(define trace-missing-cmds? #f)
(define supported-cmds '())

(define (trace-missing-bgp cmd value)
  (when trace-missing-bgp? (displayln cmd))
  value)

(define (trace-missing-policy cmd value)
  (when trace-missing-policy? (displayln cmd))
  value)

(define (trace-missing-bgp-enable!)
  (set! trace-missing-bgp? #t))

(define (trace-missing-policy-enable!)
  (set! trace-missing-policy? #t))

(define (supported-cmds-append cmds)
  (set! supported-cmds (append cmds supported-cmds))
  cmds)
