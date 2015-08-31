#lang s-exp rosette

(require "../util/util.rkt")
(require "../network/network.rkt")
(require "trace.rkt")
(require "parser.rkt")
(require "../config/config.rkt")

(provide (all-defined-out))

; general commands
(define (cidrv4? e)
  (and (pair? e) (eq? 'cidr (car e))))

(define (ipv4? e)
  (and (pair? e) (eq? 'ip (car e))))

(define (command? tag cmd)
  (define tags (listify tag))
  (define r (list-prefix? tags cmd))
  (when r (supported-cmds-append (list cmd)))
  r)

(define (command t c) 
  (define e (memf (lambda (e) (command? t e)) c))
  (if (false? e) (list t '()) (car e)))

(define (commands t c) 
  (filter (lambda (e) (command? t e)) c))

(define (children c) (last c))

; we have the following naming convention for translation functions
; translate-*       translates the * command
; translate-*-cmd   translates a cmd inside the * command
; translate-*-cmds  translates the list of cmds inside the * command

; ip translation

(define (translate-ip cmd)
  (ip (second cmd) (third cmd) (fourth cmd) (fifth cmd)))

(define (translate-cidr cmd)
  (cidr (translate-ip (second cmd)) (third cmd)))

; neighbor translation

(define (translate-neighbor cmd neighbor0)
  (define ip (translate-ip (second cmd)))
  (define neighbor1 (neighbor-ip-set neighbor0 ip))
  (car (translate-bgp-cmds (children cmd) neighbor1)))

; TODO check that import/export statements actually append and don't overwrite 
(define (translate-import cmd neighbor)
  (define policies (listify (second cmd)))
  (neighbor-import-update neighbor (lambda (ps) (append ps policies))))

(define (translate-export cmd neighbor)
  (define policies (listify (second cmd)))
  (neighbor-export-update neighbor (lambda (ps) (append ps policies))))

(define (translate-group cmd neighbor)
  (cons neighbor (cdr (translate-bgp-cmds (children cmd) neighbor))))

(define (ipv4-neighbor? cmd)
  (and (command? 'neighbor cmd)
       (ipv4? (second cmd))))

(define (add-neighbor-policy cmd neighbor)
  (let ([policy (list (term '() (translate-then-cmd cmd)))])
    (neighbor-import-update neighbor (lambda (ps) (cons policy ps)))))

(define (translate-bgp-cmd cmd neighbor)
  (cond
    [(ipv4-neighbor? cmd) (cons neighbor (list (translate-neighbor cmd neighbor)))]
    [(command? 'group cmd)    (translate-group cmd neighbor)]
    [(command? 'export cmd)   (cons (translate-export cmd neighbor) '())]
    [(command? 'import cmd)   (cons (translate-import cmd neighbor) '())]
    [(command? 'local-preference cmd) (cons (add-neighbor-policy cmd neighbor) '())]
    [(command? 'type   cmd)   (cons (neighbor-type-set neighbor (second cmd)) '())]
    [else (trace-missing-bgp cmd (cons neighbor '()))]))

; we interpret the bgp section as a program that generates a list of neighbors
; each command takes the current-neighbor, and returns a potentially modifed
; current-neighbor, and a list of newly created neighbors.
;
; neighbor -> (neighbor . [neighbor])
(define (translate-bgp-cmds cmds neighbor0)
  (if (null? cmds)
    (cons neighbor0 '())
    (let* ([cmd        (car cmds)]
           [cmds       (cdr cmds)]
           [t1         (translate-bgp-cmd cmd neighbor0)]
           [neighbor1  (car t1)]
           [neighbors1 (cdr t1)]
           [t2         (translate-bgp-cmds cmds neighbor1)]
           [neighbor2  (car t2)]
           [neighbors2 (cdr t2)])
      (cons neighbor2 (append neighbors1 neighbors2)))))

(define default-neighbor (neighbor #f 'external '() '()))

(define (translate-neighbors config)
  (define protocol-cmds (children (command 'protocols config)))
  (define bgp-cmds      (children (command 'bgp protocol-cmds)))
  (cdr (translate-bgp-cmds bgp-cmds default-neighbor)))
  
; policy translation

(define (translate-then-cmd cmd)
  (cond
    [(command? '(next term) cmd) (list (next-term))]
    [(command? '(next policy) cmd) (list (next-policy))]
    [(command? '(community add) cmd) (list (community-add (third cmd)))]
    [(command? '(community delete) cmd) (list (community-delete (third cmd)))]
    [(command? 'local-preference cmd) (list (local-preference (second cmd)))]
    [(command? 'accept cmd) (list (accept))]
    [(command? 'reject cmd) (list (reject))]
    [else (trace-missing-policy cmd '())]))

(define (translate-then cmd)
  ; there are two valid formats:
  ; - multiple actions are stored as a list in the then/from command
  ; - the action is stored directly in the then/from command
  (if (and (= 2 (length cmd)) (list? (second cmd)))
    (append-map translate-then-cmd (second cmd))
    (translate-then-cmd (cdr cmd))))

(define (is-subnet-length? s) (eq? (car s) 'subnet-length))
(define (is-subnet-length-range? s) (eq? (car s) 'subnet-length-range))

(define (is-route-filter? cmd) (and (>= (length cmd) 3) 
                                    (command? 'route-filter cmd)
                                    (cidrv4? (second cmd))))

(define (translate-route-filter-action args)
  (if (empty? args)
      '()
      (translate-then-cmd args)))

(define (translate-route-filter cmd)
  (cond
   [(member (third cmd) '(exact longer orlonger))
    (route-filter (translate-cidr (second cmd)) (third cmd) (translate-route-filter-action (cdddr cmd)))]
   [(and (eq? (third cmd) 'upto) (is-subnet-length? (fourth cmd)))
    (route-filter (translate-cidr (second cmd))
                  (upto (second (fourth cmd)))
                  (translate-route-filter-action (cddddr cmd)))]
   [(and (eq? (third cmd) 'prefix-length-range) (is-subnet-length-range? (fourth cmd)))
    (route-filter (translate-cidr (second cmd))
                  (prefix-length-range (second (fourth cmd)) (third (fourth cmd)))
                  (translate-route-filter-action (cddddr cmd)))]
   [else (trace-missing-policy cmd)]))

(define (translate-from-cmd cmd) 
  (cond
    [(command? 'prefix-list-filter cmd) (list (prefix-list-filter (second cmd) (third cmd)))]
    [(command? 'prefix-list cmd) (list (prefix-list (second cmd)))]
    [(command? 'community cmd) (map community (listify (second cmd)))]
    [(command? 'as-path cmd) (list (as-path (second cmd)))]
    [(is-route-filter? cmd) (list (translate-route-filter cmd))]
    [else (trace-missing-policy cmd '())]))

(define (translate-from cmd) 
  (if (and (= 2 (length cmd)) (list? (second cmd)))
    (append-map translate-from-cmd (second cmd))
    (translate-from-cmd (cdr cmd))))

(define (translate-term cmd)
  (define cs (children cmd))
  (define froms (translate-from (command 'from cs)))
  (define thens (translate-then (command 'then cs)))
  (term froms thens))

(define (translate-policy-statement-cmd cmd)
  (cond
    [(command? 'term cmd) (list (translate-term cmd))]
    [else (trace-missing-policy cmd '())]))

; TODO counting might be slightly wrong in here
(define (massage-policy-statement-terms terms)
  (cond
   [(empty? terms) terms]
   [(command? 'then (car terms)) (cons `(term (,(car terms)))
                                   (massage-policy-statement-terms (cdr terms)))]
   [(command? 'from (car terms))
    (if (or (empty? (cdr terms))
            (not (command? 'then (cadr terms))))
        (trace-missing-policy (car terms) (massage-policy-statement-terms (cdr terms)))
        (cons `(term (,(car terms) ,(cadr terms))) (massage-policy-statement-terms (cddr terms))))]
   [else (cons (car terms) (massage-policy-statement-terms (cdr terms)))]
   ))

(define (translate-policy-statement cmd)
  (cons (second cmd)
        (append-map translate-policy-statement-cmd (massage-policy-statement-terms (children cmd)))))

(define (all-policies neighbors)
  (remove-duplicates (append-map identity (append-map (lambda (n) (list (neighbor-import n) (neighbor-export n))) neighbors))))

(define (translate-policies config policy-names)
  (define policy-option-cmds (children (command 'policy-options config)))
  (define policy-statements (commands 'policy-statement policy-option-cmds))
  ; TODO translate also unreferenced policy statements so we count them as supported,
  ; we might want to disable tracing during this time
  ; (filter identity (map (lambda (p) (if (member (second p) policy-names) (translate-policy-statement p) #f)) policy-statements)))
  (map translate-policy-statement policy-statements))

; prefix-list translation

; TODO is this really a command?
(define (prefix-list-ip? cmd)
  (define b (and (list? cmd) 
                 (= 1 (length cmd))
                 (cidrv4? (car cmd))))
  (when b (supported-cmds-append (list cmd)))
  b)

(define (translate-prefix-list-cmd cmd)
  (cond
    [(prefix-list-ip? cmd) (list (translate-cidr (car cmd)))]
    [else                  '()]))

(define (translate-prefix-list cmd)
  (cons (second cmd)
    (if (= 2 (length cmd))
      '()
      (append-map translate-prefix-list-cmd (children cmd)))))

(define (translate-prefix-lists config)
  (define policy-option-cmds (children (command 'policy-options config)))
  (define prefix-lists (commands 'prefix-list policy-option-cmds))
  (map translate-prefix-list prefix-lists))

; router options translation

(define (default-router ip) (router ip '()))

; http://www.juniper.net/techpubs/en_US/junos12.1/topics/reference/configuration-statement/router-id-edit-routing-options.html
(define (translate-routing-options config)
  (define routing-options-cmds (children (command 'routing-options config)))
  (define cmd (command 'router-id routing-options-cmds))
  (default-router (translate-ip (second cmd))))

; full config translation

(define (inline-policies neighbors policies)
  (define (lookup ps)
    (map (lambda (p) (if (pair? p) p (cdr (assoc p policies)))) ps))

  (map (lambda (n0)
    (let* ([n1 (neighbor-import-update n0 lookup)]
           [n2 (neighbor-export-update n1 lookup)])
      n2)
  ) neighbors))

(define (inline-prefix-lists policies prefix-lists)
  (define (lookup pl)
    (cdr (assoc pl prefix-lists)))

  (map (lambda (policy)
    (cons (car policy)
      (map (lambda (trm)
        (term 
          (map (lambda (from)
            (cond
              [(prefix-list? from) (prefix-list (lookup (prefix-list-list from)))]
              [(prefix-list-filter? from) (prefix-list-filter (lookup (prefix-list-filter-list from))
                                                              (prefix-list-filter-modifier from))]
              [else from])
          ) (term-froms trm))
          (term-thens trm))
      ) (cdr policy)))
  ) policies))

(define (translate-config config)
  (define ns (translate-neighbors config))
  (define ps (translate-policies config (all-policies ns)))
  (define ls (translate-prefix-lists config))
  (define r  (translate-routing-options config))
  (router-neighbors-update [lambda (_)
    (inline-policies ns (inline-prefix-lists ps ls))
  ] r))

; TODO, this also counts inactive commands as commands
(define (count-commands cmds)
  (define (commands? v)
    (and (list? v) (andmap pair? v)))

  (if (commands? cmds)
    (apply + (map [lambda (cmd) (add1 (count-commands (children cmd)))] cmds))
    0))

(define (load-router config-file)
  (write-string (string-append (~a config-file) "\n")) (flush-output)
  (translate-config (juniper->sexp config-file)))

(define (load-as config-files)
  (as (map load-router config-files)))
