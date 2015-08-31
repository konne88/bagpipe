#lang s-exp rosette

(require rackunit)

(require "../main/util/util.rkt")
(require "../main/juniper/parser.rkt")
(require "../main/juniper/translate.rkt")
(require "resources/internet2-properties.rkt")

(define pops '("atla" "chic" "clev" "hous" "kans" "losa" "newy32aoa" "salt" "seat" "wash"))
(define config-files (map [lambda (pop) (bagpipe-path (string-append "configs/internet2/" pop ".conf"))] pops))
(define peers (infer-peers config-files))

(test-case
  "peers inference tests"
  (check eq? peers internet2-peers))
