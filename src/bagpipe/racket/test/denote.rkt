#lang s-exp rosette/safe

; TODO, what is the scope of this statement?
; needed for local-preference
(current-bitwidth 10)

(require rackunit)
(require rosette/lib/meta/meta)

(require "../main/util/util.rkt")
(require "../main/network/network.rkt")
(require "../main/config/config.rkt")
(require "../main/config/denote.rkt")
(require "../main/config/environment.rkt")
(require "resources/simple-contract.rkt")

(test-case
  "prefix compare tests"
  (define subnet (cidr (ip 192 168 0 0) 16))
  (check-true  (prefix-compare 'exact    subnet subnet))
  (check-true  (prefix-compare 'exact    subnet (cidr (ip 192 168 1 3) 16)))
  (check-true  (prefix-compare 'orlonger subnet subnet))
  (check-true  (prefix-compare 'orlonger subnet (cidr (ip 192 168 1 0) 24)))
  (check-true  (prefix-compare 'longer   subnet (cidr (ip 192 168 1 0) 24)))
  (check-false (prefix-compare 'exact    subnet (cidr (ip 192 168 0 0)  8)))
  (check-false (prefix-compare 'orlonger subnet (cidr (ip 192   0 0 0)  8)))
  (check-false (prefix-compare 'longer   subnet (cidr (ip 192 168 0 0) 16)))
  (check-false (prefix-compare 'longer   subnet (cidr (ip 192   0 0 0)  8))))


(define env (environment '(DISCARD MAKE-LOW LOW OTHER) '(COMMERCIAL PRIVATE)))

(define given-subnet (cidr (ip 192 168 0 0) 16))

(test-case 
  "denote term test"
  (define match-prefix  (default-announcement (cidr (ip 192 168   1   0) 24) env))
  (define other-prefix (default-announcement (cidr (ip  65 123  96   0) 24) env))
  (define discard-community (announcement-community-set other-prefix 'DISCARD true))

  (define rf (route-filter given-subnet 'orlonger (list (community-add 'LOW))))

  (check-false (denote-route-filter rf other-prefix))
  (check eq? (denote-route-filter rf match-prefix)
    (list (community-add 'LOW)))

  (check-false (denote-froms (list rf) other-prefix))
  (check eq? (denote-froms (list rf) match-prefix)
    (list (community-add 'LOW)))

  (check eq? (denote-froms '() other-prefix) '())

  (define trm (term (list rf) (list (community-add 'OTHER))))

  (check eq? (denote-term trm other-prefix) (flow 'next-term other-prefix))
  
  (check-true (announcement-community-test 
    (flow-announcement (denote-term trm match-prefix)) 'LOW))

  (define rf-null (route-filter given-subnet 'orlonger '()))
  (check eq? (denote-route-filter rf-null match-prefix) '())

  (define trm-null (term (list rf-null) (list (community-add 'OTHER))))
  (check-true (announcement-community-test 
    (flow-announcement (denote-term trm-null match-prefix)) 'OTHER)))

(define given-policies (list
  (list ; policy
    (term
      (list (route-filter given-subnet 'orlonger '())) ; from
      (list (reject))  ; then
    )
    (term
      (list (community 'DISCARD)) ; from
      (list (reject))  ; then
    )
  )))

(define (process a) (denote-policies given-policies a))

(define (check-profitable? a)
  (makes-profit? simple-contract given-policies a))

(test-case
  "denote tests"
  (define bad-prefix  (default-announcement (cidr (ip 192 168   1   0) 24) env))
  (define good-prefix (default-announcement (cidr (ip  65 123  96   0) 24) env))
  (define discard-community (announcement-community-set good-prefix 'DISCARD true))

  (check-pred accepted? (process good-prefix))
  (check-pred rejected? (process bad-prefix))
  (check-pred rejected? (process discard-community))

  (check-true (check-profitable? good-prefix))
  (check-true (check-profitable? bad-prefix))
  (check-true (check-profitable? discard-community)))

"==== SYNTHESIZE ===="

(define-synthax (synthesize-community)
  (choose 'LOW 'OTHER 'MAKE-LOW 'DISCARD))

(define-synthax (synthesize-aspath)
  (choose 'PRIVATE 'COMMERCIAL))

; TODO, synthesis appears to reach undefined then/from commands in denote
; if there are more than 2 choices available. we can see this by incerting a
; print statement in the else branch
(define-synthax (synthesize-from) (list
  (choose
    (as-path (synthesize-aspath))
    (community (synthesize-community))
    (route-filter (cidr (ip (??) (??) (??) (??)) (??)) 'orlonger '()))))

(define-synthax (synthesize-then) (list
  (choose
    (community-add (synthesize-community))
    (reject)
    (next-term)
    (accept))))

(define-synthax (synthesize-policy k)
  #:assert (>= k 0)
  (choose
    '()
    (cons (term (synthesize-from) (synthesize-then)) (synthesize-policy (sub1 k)))))

(define-synthax (synthesize-policies k) 
  (list (synthesize-policy k)))

(define template-policies (synthesize-policies 3))

(define sa (symbolic-announcement env))

(define binding (synthesize
  #:forall (list sa)
  #:guarantee (assert (makes-profit? simple-contract template-policies sa))))

(print-forms binding)
