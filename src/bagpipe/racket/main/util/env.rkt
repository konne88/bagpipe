#lang s-exp rosette

(provide bagpipe-root bagpipe-path)

(define (bagpipe-root)
  (define e (getenv "BAGPIPE"))
  (if e (expand-user-path e) "/bagpipe"))

(define (bagpipe-path . args)
  (apply build-path (cons (bagpipe-root) args)))
