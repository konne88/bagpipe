#lang s-exp rosette

(require rosette/solver/smt/z3)
(require racket/format)

(current-bitwidth 10)
(current-solver (new z3%))

(require "util/list.rkt")
(require "util/rosette.rkt")
(require "util/extraction.rkt")
(require "network/network.rkt")
(require "config/environment.rkt")
(require "config/denote.rkt")
(require "config/config.rkt")
(require "setup.rkt")
(require racket/place)
(require racket/place/distributed)

(provide bgpv bgpvImport bgpv-place)

(define routing-batch-size 32)

(define (coq-list-length l)
  (match l
    ((Nil) 0)
    ((Cons _ l*) (add1 (coq-list-length l*)))))
   
(define (bgpv-place ch)
  (define setup (place-channel-get ch))
  (define query (place-channel-get ch))
  (define (loop n)
    (if (eq? n routing-batch-size) (void) (begin
;     (clear-asserts)
;     (unsafe-clear-terms!)
      (define routing (place-channel-get ch))
      (define res (@ bgpvCore~ setup query routing))
      (place-channel-put ch (@ optionToSpace listSpaceSearch res))
      (loop (add1 n)))))
  (loop 0))

(define (cpus) ; '(1))
  (match-let ([(list out in pid err ctrl) (process "nproc")])
    (ctrl 'wait)
    (define res (read-line out))
    (close-output-port in)
    (close-input-port out)
    (close-input-port err)
    (in-range (string->number res))))

(define (nodes)
  (define evars (environment-variables-names (current-environment-variables)))
  (append* (list "localhost") (for/list ([evar evars])
    (define r (regexp-match #rx"^([^_]+)_NAME$" evar))
    (if r (list (string-downcase (bytes->string/utf-8 (second r)))) '()))))

(define distributed-bgpv-scheduler (lambdas (setup query routings)
  (define checks (coq-list-length routings))
  (write-string (string-append "total number of checks " (~a checks) "\n"))
  (flush-output)

  (define work-queue (make-channel))
  (define thd (current-thread))

  ; start threads/nodes
  (for*/list ([node (nodes)] [cpu (cpus)])
    (thread (lambda ()
      (define nd (create-place-node node #:listen-port (+ 1234 cpu)))
      (define (loop)
        (define ch (dynamic-place #:at nd (quote-module-path) 'bgpv-place))
        (place-channel-put ch setup)
        (place-channel-put ch query)
        (define (inner-loop n)
          (if (eq? n routing-batch-size) (void) (begin
            (define routing (channel-get work-queue))
            (place-channel-put ch routing)
            (define res (place-channel-get ch))
            (thread-send thd res)
            (inner-loop (add1 n)))))
        (inner-loop 0)
        (loop))
      (loop))))

  ; provide work for threads
  (define (enqueue routings counter)
    (match routings
      ((Nil) (void))
      ((Cons routing routings*) (begin
        (channel-put work-queue routing)
        (write-string (string-append "check " (~a counter) "\n")) (flush-output)
        (enqueue routings* (add1 counter))))))
  (enqueue routings 0)

  ; collect results
  (@ search listSpaceSearch
    (@ bind listSpaceSearch routings (lambda (_)
      (thread-receive))))))

(define denote-query (lambdas (prop r i o p ai al ae)
  (if ((load-prop prop) r i o p ai al ae) '(True) '(False))))

(define denote-import (lambdas (as r i p a) (begin
  (define r* (as-routers-lookup as r))
  (define policies (match i
    ((Injected) 
      ; TODO enable static route configurations
      (list (list (term (list) (list (reject))))))
    ((Received record)
      (match record ((ExistT record _)  ; connection
      (match record ((ExistT __ i*) ; internal/external
        (neighbor-import (router-neighbors-lookup r* i*)))))))))
  ; TODO figure out a better way to deal with p
  (define res (denote-policies policies (announcement-prefix-set a p)))
  (if (accepted? res)
    `(Available ,(flow-announcement res))
    `(NotAvailable)))))

(define denote-export (lambdas (as r o p a) (begin
  (define r* (as-routers-lookup as r))
  (define o* (match o ((ExistT record _)  ; connection
             (match record ((ExistT __ o*) ; internal/external
               o*)))))
  (define policies (neighbor-export (router-neighbors-lookup r* o*)))
  ; TODO figure out a better way to deal with p
  (define res (denote-policies policies (announcement-prefix-set a p)))
  (if (accepted? res)
    `(Available ,(flow-announcement res))
    `(NotAvailable)))))

(define eq-dec? (lambdas (a b) (if (eq? a b) '(Left) '(Right))))

