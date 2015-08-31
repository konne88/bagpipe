#lang s-exp rosette

(provide solve/evaluate/concretize)

(define (concretize-solution m consts)
  (sat (for/hash ([c consts]) 
         (match (m c)
           [(constant _ (== number?))
            (values c 0)]
           [(constant _ (== boolean?))
            (values c #f)]
           [(constant _ (? enum? t))
            (values c (enum-first t))]
           [val (values c val)]))))

(define-syntax-rule (solve/evaluate/concretize expr)
  (with-handlers ([exn:fail? (lambda (e) '(None))])
    (let ([v (solve/evaluate (expr void))])
      `(Some ,(evaluate v (concretize-solution (current-solution) (symbolics v))))))) 
