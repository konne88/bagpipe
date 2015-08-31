#lang racket
(require srfi/13)

(require "../util/util.rkt")
(provide juniper->sexp paths-set->sexp)

(define juniper-sexp-path (bagpipe-path "src/bagpipe/hs/dist/build/juniper-sexp/juniper-sexp"))


(define ip-regexp #px"^(\\d+)\\.(\\d+)\\.(\\d+)\\.(\\d+)(?:/(\\d+))?$")
(define (ip? s)
  (and (string? s)
       (regexp-match? ip-regexp s)))

(define (convert-ip-helper b1 b2 b3 b4)
  `(ip ,(string->number b1) ,(string->number b2)
       ,(string->number b3) ,(string->number b4)))

(define (convert-ip ip)
  (let ([matches (regexp-match ip-regexp ip)])
    (match (cdr matches)
      [`(,b1 ,b2 ,b3 ,b4 #f) (convert-ip-helper b1 b2 b3 b4)]
      [`(,b1 ,b2 ,b3 ,b4 ,mask) `(cidr ,(convert-ip-helper b1 b2 b3 b4) ,(string->number mask))]
      )
    )
  )

(define (parse-ips c)
  (cond
   [(list? c) (map parse-ips c)]
   [(ip? c) (convert-ip c)]
   [else c]))

(define subnet-regexp #px"^/(\\d+)$")
(define subnet-range-regexp #px"^/(\\d+)-/(\\d+)$")

(define (paths-set->sexp paths-set-str)
  (read (open-input-string paths-set-str)))

(define (parse-subnet s)
  (let ([matches (regexp-match subnet-regexp s)])
    `(subnet-length ,(string->number (cadr matches)))))

(define (parse-subnet-range s)
  (let ([matches (regexp-match subnet-range-regexp s)])
    `(subnet-length-range ,(string->number (cadr matches)) ,(string->number (caddr matches)))))

(define (parse-subnet-string s)
  (cond
   [(regexp-match? subnet-regexp s) (parse-subnet s)]
   [(regexp-match? subnet-range-regexp s) (parse-subnet-range s)]
   [else s]))

(define (parse-subnets c)
  (cond
   [(list? c) (map parse-subnets c)]
   [(and (symbol? c) (string-prefix? "/" (symbol->string c))) (parse-subnet-string (symbol->string c))]
   [else c]))

(define (postprocess c)
  (parse-subnets (parse-ips (car c))))

(define (juniper->sexp file)
  (define-values (process out in err) 
    (apply subprocess #f #f #f juniper-sexp-path (list  file)))
  (with-handlers ([exn:break? (lambda (e) 
                                (subprocess-kill process #t)
                                (error 'solve "user break"))])
    (postprocess (read out))))
