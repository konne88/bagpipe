#lang s-exp rosette/safe

(current-bitwidth 10)

(require rackunit)
(require rosette/lib/meta/meta)

(require "../main/util/util.rkt")
(require "../main/network/network.rkt")
(require "../main/juniper/parser.rkt")
(require "../main/juniper/translate.rkt")
(require "../main/config/config.rkt")
(require "../main/config/environment.rkt")
(require "../main/config/denote.rkt")
(require "resources/internet2-properties.rkt")
(require "resources/indiana-gigapop.rkt")
(require "../main/bagpipe.rkt")
(require "../main/configs.rkt")

(define i2 (load-config "internet2-atla"))
(define atla (first (as-routers i2)))
(define atla-neighbors (router-neighbors atla))
(define atla-ingp (findf indiana-gigapop? atla-neighbors))
(define peers (infer-peers (list (bagpipe-path "configs/internet2/atla.conf"))))

; NOTE the FLR client (108.59.25.20) used to fail verify.  I couldn't
; figure out why, just by looking at the config. I only realized that is was
; caused by the lack of support for `then` as a shorthand for `term`, once I
; implemented support for it. It would have be cool to see which terms fired and
; modifed the announcement/resulted in an accept or reject.

(test-case
  "test atlanta parsing/translation/denotation"
  (check eq? atla-itns peers)

  (check eq? atla-ingp ingp))
