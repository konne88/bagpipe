#lang s-exp rosette

(provide verify* solve* undefined write->string)

; returns #f because the true branch of an if is triggered by everything else
(define-syntax-rule (verify* expr)
  (with-handlers ([exn:fail? (lambda (e) #f)])
    (verify expr)))

(define-syntax-rule (solve* expr)
  (with-handlers ([exn:fail? (lambda (e) #f)])
    (solve expr)))

; TODO improve error handling, introduce contracts (preconditions) etc
(define undefined 'error)

(define (write->string v)
  (define dst (open-output-string))
  (write v dst)
  (get-output-string dst))
