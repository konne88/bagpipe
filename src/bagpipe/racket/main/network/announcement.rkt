#lang s-exp rosette

(require "../util/util.rkt")
(require "ip.rkt")
(require "prefix.rkt")

(provide default-announcement announcement?
         announcement-prefix announcement-prefix-set
         announcement-community-test announcement-community-set
         announcement-aspath-test announcement-aspath-set
         announcement-pref announcement-pref-set
         environment environment-merge
         count-aspaths count-communities
         environment-aspaths environment-communities
         symbolic-announcement)

(define (announcement communities prefix aspath pref) 
  `(Announcement ,communities ,prefix ,aspath ,pref))
(define (announcement? a) (and (pair? a) (eq? (first a) 'Announcement)))
(define (announcement-communities a) (second a))
(define (announcement-prefix a) (third a))
(define (announcement-aspath a) (fourth a))
(define (announcement-pref a) (fifth a))

(define (announcement-aspath-set a p b)
  (announcement (announcement-communities a)
                (announcement-prefix a)
                (subset-set (announcement-aspath a) p b)
                (announcement-pref a)))

(define (announcement-aspath-test a p)
  (subset-ref (announcement-aspath a) p))

(define (announcement-community-set a c b)
  (announcement (subset-set (announcement-communities a) c b) 
                (announcement-prefix a) 
                (announcement-aspath a)
                (announcement-pref a)))

(define (announcement-community-test a c)
  (subset-ref (announcement-communities a) c))

(define (announcement-prefix-set a prefix)
  (announcement (announcement-communities a)
                prefix
                (announcement-aspath a)
                (announcement-pref a)))

(define (announcement-pref-set a pref)
  (announcement (announcement-communities a)
                (announcement-prefix a) 
                (announcement-aspath a)
                pref))

(define (environment communities aspaths) `(Environment ,communities ,aspaths))
(define (environment? c) (and (pair? c) (eq? 'Environment (first c))))
(define (environment-communities c) (second c))
(define (environment-aspaths c) (third c))

(define (count-communities env)
  (length (environment-communities env)))

(define (count-aspaths env)
  (length (environment-aspaths env)))

(define (environment-merge es)
  (environment (remove-duplicates (flatten (map environment-communities es)))
               (remove-duplicates (flatten (map environment-aspaths es)))))

; TODO representing communities and aspaths as sets of juniper community/aspaths
; is potentially unsafe. For example, imagine the following communities:
; A = 3
; B = 5
; C = 3 and 5
; dicarding all annoucements with C set, also discards all annoucements with A
; or B set, but we wouldn't know. We could solve this by adding additional
; constraints between an annoucement's boolean variables, e.g. C -> A /\ B.
(define (default-announcement prefix env)
  (announcement
    (subset (environment-communities env))
    prefix
    (subset (environment-aspaths env))
    200))

(define (symbolic-communities env)
  (symbolic-subset (environment-communities env)))

(define (symbolic-aspath env)
  (symbolic-subset (environment-aspaths env)))

(define (symbolic-announcement env)
  (define prefix (symbolic-prefix))
  (define comms (symbolic-communities env))
  (define aspath (symbolic-aspath env))
  (define-symbolic* pref number?)
  (announcement comms prefix aspath pref))
