#lang racket

(require "util/util.rkt")
(require "network/network.rkt")
(require "juniper/parser.rkt")
(require "config/denote.rkt")
(require "juniper/translate.rkt")
(require "juniper/trace.rkt")
(require "config/environment.rkt")
(require "util/extraction.rkt")
(require "setup.rkt")
(require "bgpv.rkt")

(provide verify verify? help)

(define (format-ip ip)
  (string-join (list
    (~a (bits->number (take (drop (ip-bits ip)  0) 8)))
    (~a (bits->number (take (drop (ip-bits ip)  8) 8)))
    (~a (bits->number (take (drop (ip-bits ip) 16) 8)))
    (~a (bits->number (take (drop (ip-bits ip) 24) 8)))
  ) "."))

(define (center-ip ip)
  (~a (format-ip ip) #:align 'center #:min-width 15))

(define (format-cidr cidr)
  (match cidr ((Prefix ip len) (string-append (format-ip ip) "/" (~a len)))))

(define (format-subset s)
  (string-append "[" (string-join (map ~a (subset->list s)) ", ") "]"))

(define (format-announcement a)
  (if (eq? a 'not-available) 
    "not-available"
    (match a ((Announcement coms p path pref)
      (string-append "{pref: " (~a pref) 
                     ", coms: " (format-subset coms) 
                     ", path: " (format-subset path) "}")))))

(define (format-path suffix path)
  (if (or (empty? path) (empty? (cdr path)))
    (list
      (string-append "                             ")
      (string-append "                                ")
      (string-append "                                ")
      (string-append "                                |  ")
      (string-append "                                "))
  (if (empty? (cddr path))
    (list
      (string-append (center-ip (cadr path)) "              ")
      (string-append "    ______                      ")
      (string-append "   |      |                     ")
      (string-append "   | a0" suffix " -|---------------------|->")
      (string-append "   |______|                     "))
    (list
      (string-append (center-ip (caddr path)) "              ")
      (string-append "    ______                      ")
      (string-append "   |      |    " (center-ip (cadr path)) "  ")
      (string-append "   | a0" suffix " -|--------->[]---------|->")
      (string-append "   |______|                     ")))))

(define (format-counter-example r i o p ai0 aip ai0* aip* ai ai* al ae)
  (define s (append (list "                                ")
                    (format-path "*" aip*) 
                    (list "                                ")
                    (format-path " " aip )))
  (define t (list
    (string-append    "     " (center-ip r))
    (string-append "    ___________________ ")
    (string-append    "| in   . loc .  out |")
    (string-append    "|      .     .      |")
    (string-append       " ai*.     .      |")
    (string-append    "|    , .     .      |")
    (string-append    "|    | .     .      |  " (center-ip o))
    (string-append "   |    '-> al -> ae --|------->[]")
    (string-append    "|      .     .      |")
    (string-append    "|      .     .      |")
    (string-append       " ai .     .      |")
    (string-append    "|______._____.______|")))
  (define st (map string-append s t))
  (define u (list
    (string-append "")
    (string-append "p   = " (format-cidr p))
    (string-append "a0  = " (format-announcement ai0))
    (string-append "a0* = " (format-announcement ai0*))
    (string-append "ai  = " (format-announcement ai))
    (string-append "ai* = " (format-announcement ai*))
    (string-append "al  = " (format-announcement al))
    (string-append "ae  = " (format-announcement ae))))
  (string-join (append st u) "\n"))

(define (format-counter-example-import r i o p ai0 aip ai0* aip* ai ai* al ae)
  (define s (format-path " " aip))
  (define t (list
    (string-append (center-ip r))
    (string-append " ______ ")
    (string-append "|      |")
    (string-append    " al |")
    (string-append "|______|")))
  (define st (map string-append s t))
  (define u (list
    (string-append "")
    (string-append "p  = " (format-cidr p))
    (string-append "a0 = " (format-announcement ai0*))
    (string-append "al = " (format-announcement al))))
  (string-join (append st u) "\n"))

(define (path->list path)
  (match path 
    ((Start r) (match r ((ExistT rt r) 
      (list r))))
    ((Hop _ r rc path) (match r ((ExistT rt r)
      (cons r (path->list path)))))))

(define (unpack-tracking a f)
  (match a
    ((NotAvailable)
      (f 'not-available 'not-available '()))
    ((Available a)
      (match a 
        ((Build_Tracking a0 a path) 
          (f a0 a (path->list path)))))))

(define (unpack-incoming i f)
  (match i 
    ((Injected) (f 'injected))
    ((Received i)
      (match i ((ExistT record ic)   ; connection
      (match record ((ExistT it i)   ; router  type
        (f i))))))))

(define (unpack-counter-example record f)
  ; unpack tuple
  (match record ((ExistT r record)
  (match record ((Pair record ae)
  (match record ((Pair record al)
  (match record ((Pair record ai*)
  (match record ((Pair record ai)
  (match record ((Pair record p)
  (match record ((Pair i o)
  ; unpack o
  (match o ((ExistT record oc)   ; connection 
  (match record ((ExistT ot o)   ; router type
  ; unpack i
  (unpack-incoming i (lambda (i)
  ; unpack tracking
  (unpack-tracking ai  (lambda (ai0  ai  aip )
  (unpack-tracking ai* (lambda (ai0* ai* aip*)
  (unpack-tracking al  (lambda (al0  al  alp )
  (unpack-tracking ae  (lambda (ae0  ae  aep )
    (f r i o p ai0 aip ai0* aip* ai ai* al ae))))))))))))))))))))))))))))))

(define (verify args)
  (write-string "loading as\n") (flush-output)
  (define as (load-config args))
  (write-string "done loading as\n") (flush-output)
  (load-prop args)  ; for better error reporting
  ; NOTE the complexity for is a single internal router with n neighbors is 
  ; 4n^3 + 4n^2 + n 
  (define res (@ bgpvImport as args))
  (write-string (match res
    ((Some record) (unpack-counter-example record format-counter-example-import))
    ((None) "holds")))
  (write-string "\n")
  (flush-output))

(define (verify? args)
  (and (>= (length args) 2)
       (equal? (first args) "verify")))

(define (help)
  (displayln #<<HELP
Usage: bagpipe COMMAND

The bagpipe commands are:
   verify SETUP ARGS     Verifies the setup in SETUP/setup.rkt. setup.rkt
                         must define two variables called `as` and a `policy`;
                         the former defines the AS that bagpipe verifies using 
                         the POLICY defined by the latter. ARGS is passed to 
                         both the AS and POLICY.

   help                  Display this help message and exit.
HELP
   ))

(module+ main
  (define cl-args (vector->list (current-command-line-arguments)))
  (cond
    [(verify? cl-args) (verify (cdr cl-args))]
    [else (help)]))
