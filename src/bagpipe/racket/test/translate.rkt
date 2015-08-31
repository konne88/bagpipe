#lang s-exp rosette/safe

(current-bitwidth 10)

(require rackunit)
(require rosette/lib/meta/meta)

(require "../main/util/util.rkt")
(require "../main/network/network.rkt")
(require "../main/juniper/translate.rkt")
(require "../main/config/environment.rkt")
(require "../main/config/config.rkt")
(require "resources/simple-contract.rkt")

(define test-ip '(ip 192 168 1 0))

(define test-neighbors `(
  (protocols (
    (bgp (
      (export Q)
      (group I2 (
        (neighbor ,test-ip (
          (type external)
          (import P)
        ))
      ))
    ))
  ))
))

(define translated-neighbors
  (list (neighbor (translate-ip test-ip) 'external '(P) '(Q))))

(test-case
  "neighbor translation tests"
  (check eq? (neighbor #f 'external '(A) '()) 
    (translate-import `(import A) default-neighbor))

  (check eq? (cons (neighbor #f 'external '(A) '()) '())
    (translate-bgp-cmds `((import A)) default-neighbor))

  (check eq? (neighbor (translate-ip test-ip) 'external '(I) '(E))
    (translate-neighbor `(neighbor ,test-ip ((import I) (export E))) default-neighbor))

  (check eq? (neighbor (translate-ip test-ip) 'external `((,(term '() (list (local-preference 200)))) I) '(E))
         (translate-neighbor `(neighbor ,test-ip ((local-preference 200)
                                                  (import I) (export E))) default-neighbor))
  
  (check eq? (cons default-neighbor (list (neighbor (translate-ip test-ip) 'external '() '())))
    (translate-bgp-cmd `(neighbor ,test-ip ()) default-neighbor))

  (check eq? (cons default-neighbor (list (neighbor (translate-ip test-ip) 'external '() '())))
    (translate-bgp-cmds `((neighbor ,test-ip ())) default-neighbor))

  (check eq? (cons default-neighbor (list (neighbor (translate-ip test-ip) 'external '() '())))
    (translate-group `(group INTERNET2 ((neighbor ,test-ip ()))) default-neighbor))

  (check eq? '() 
    (translate-neighbors '()))

  (check eq? translated-neighbors
    (translate-neighbors test-neighbors)))

(define test-policies '(
  (policy-options (
    (policy-statement P (
      (term A (
        (from (
          (route-filter (cidr (ip 0 0 0 0) 0) upto (subnet-length 24))
          (route-filter (cidr (ip 0 0 0 0) 0) prefix-length-range (subnet-length-range 24 32))
          (route-filter (cidr (ip 0 0 0 0) 0) orlonger)          
          (prefix-list-filter S orlonger)          
          (prefix-list-filter T exact)
          (as-path X)
        ))
        (then (
          (community add C) 
          (accept)
        ))
      ))
      (term B (
        (then reject)
      ))
    ))
    (policy-statement Q (
                         (term A (
                                  (from community D)
                                  ))
                         ))
    (policy-statement R (
                         (from community D) (then reject)
                         ))
  ))
))

(define translated-policies
  (list
    (cons 'P 
      (list
        (term 
         (list
            (route-filter (cidr (ip 0 0 0 0) 0) (upto 24) '())
            (route-filter (cidr (ip 0 0 0 0) 0) (prefix-length-range 24 32) '())          
            (route-filter (cidr (ip 0 0 0 0) 0) 'orlonger '())
            (prefix-list-filter 'S 'orlonger)
            (prefix-list-filter 'T 'exact)
            (as-path 'X)
          )
          (list
            (community-add 'C)
            (accept)
          )
        )
        (term
          '()
          (list (reject))
        )
      )
    )
    (cons 'Q
      (list
        (term 
          (list (community 'D))
          '()
        )
      )
      )
    (cons 'R
          (list
           (term 
            (list (community 'D))
            (list (reject))
            )
           )
          )
  )
)

(test-case
  "policy translation tests" 
  (check eq? translated-policies
    (translate-policies test-policies '(P Q R))))

(define test-prefix-lists '(
  (policy-options (
    (prefix-list S (
      ((cidr (ip 64 57 28 240) 28))
      ((cidr (ip 129 79 5 100) 32))
    ))
    (prefix-list T)
  ))
))

(define translated-prefix-lists
  (list
    (cons 'S
      (list
        (cidr (ip 64 57 28 240) 28)
        (cidr (ip 129 79 5 100) 32)
      )
    )
    (cons 'T '())
  )
)

(test-case
  "prefix translation tests" 
  (check eq? translated-prefix-lists
    (translate-prefix-lists test-prefix-lists)))

(define test-routing-options '(
  (routing-options (
    (router-id (ip 123 45 67 89))
  ))
))

(define translated-routing-options
  (router (ip 123 45 67 89) '()))

(test-case
  "routing options translation tests"
  (check eq?
    (translate-routing-options test-routing-options)
    translated-routing-options))

(test-case
  "count total commands"

  (check eq? 7 (count-commands 
    test-neighbors
  ))
)

(define test-full-config (append
  test-neighbors
  test-routing-options
  `((policy-options ,(append
    (children (car test-policies))
    (children (car test-prefix-lists))
  )))
))

(define translated-full-config 
  (router (ip 123 45 67 89)
    (list
    (neighbor (translate-ip test-ip) 'external
      (list
        (list
          (term 
            (list
             (route-filter (cidr (ip 0 0 0 0) 0) (upto 24) '())
             (route-filter (cidr (ip 0 0 0 0) 0) (prefix-length-range 24 32) '())
             (route-filter (cidr (ip 0 0 0 0) 0) 'orlonger '())
             (prefix-list-filter (list
                (cidr (ip 64 57 28 240) 28)
                (cidr (ip 129 79 5 100) 32)
              ) 'orlonger)
              (prefix-list-filter '() 'exact)
              (as-path 'X)
            )
            (list
              (community-add 'C)
              (accept)
            )
          )
          (term
            '()
            (list (reject))
          )
        )
      )
      (list
        (list
          (term 
            (list (community 'D))
            '()
          )
        )
      )
    )
  )
))

(test-case 
  "environment tests"
  (define e0 (environment '(C) '(X)))
  (check eq? (policies->environment (neighbor-import 
    (first (router-neighbors translated-full-config)))) e0)
  (define e1 (environment '(C D) '(X)))
  (check eq? (neighbors->environment (router-neighbors translated-full-config)) e1))

(test-case
  "full config tests" 
  (check eq? translated-full-config
    (translate-config test-full-config)))

"==== SYNTHESIZE ===="

(define-synthax (synthesize-community)
  (choose 'LOW 'OTHER 'MAKE-LOW 'DISCARD))

(define-synthax (synthesize-aspath)
  (choose 'PRIVATE 'COMMERCIAL))

(define-synthax (synthesize-from) (list
  (choose
    `(as-path ,(synthesize-aspath))
    `(community ,(synthesize-community))
    `(route-filter (cidr (ip ,(??) ,(??) ,(??) ,(??)) ,(??)) orlonger)
  )))

(define-synthax (synthesize-then) (list
  (choose
    `(community-add ,(synthesize-community))
    '(reject)
    '(next-term)
    '(accept)
  )))

(define-synthax (synthesize-policy k)
  #:assert (>= k 0)
  (choose
    '()
    (cons
      `(term (
         (from
           ,(synthesize-from) 
         )
         (then
           ,(synthesize-then)
         ) 
      ))
      (synthesize-policy (sub1 k)))))

(define-synthax (synthesize-policies k) `(
  (protocols (
    (bgp (
      (group G (
        (neighbor ,test-ip (
          (type external)
          (import I)
        ))
      ))
    ))
  ))
  (routing-options (
    (router-id (ip 123 45 67 89))
  ))
  (policy-options (
    (policy-statement I
      ,(synthesize-policy k)
    )
  ))
))

(define config-template (synthesize-policies 3))

(define env (environment '(DISCARD MAKE-LOW LOW OTHER) '(COMMERCIAL PRIVATE)))

(define a (symbolic-announcement env))

(define binding (synthesize             
                 #:forall (list a)
                 #:guarantee (assert (profitable? 
                                        simple-contract 
                                        (translate-config config-template)
                                        a))))

(print-forms binding)
