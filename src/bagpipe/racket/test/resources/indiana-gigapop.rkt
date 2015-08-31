#lang s-exp rosette/safe

(require "../../main/network/network.rkt")
(require "../../main/config/config.rkt")

(provide ingp ingp-communities ingp-aspaths)


(define ingp-communities '(
  (LOW                11537 140)
  (LOW-PEERS          11537 40 )
  (HIGH               11537 260)
  (HIGH-PEERS         11537 160)
  (DISCARD            11537 911)
  (SEGP               11537 910)
  (PARTICIPANT        11537 950)
  (SPONSORED          11537 902)
  (BLOCK-TO-EXTERNAL  11537 888)
  (NLR-TELEPRESENCE   65010 19401)
  (INTERNET2-INFINERA 19782 65533)
  (NO-EXPORT          no-export)
))

(define ingp-aspaths '(
  (COMMERCIAL ".* (174|701|1239|1673|1740|1800|1833|2551|2548|2685|2914|3549|3561|3847|3951|3967|4183|4200|5683|6113|6172|6461|7018) .*")
  (PRIVATE ".* (64512-65535) .*")    ; 1023 path numbers
  (NLR ".* 19401 .*") 
))

(define INTERNAL (list
  (cidr (ip 64 57 16 0) 20)  
  (cidr (ip 64 57 22 0) 24)  
  (cidr (ip 64 57 23 240) 28)  
  (cidr (ip 198 32 8 0) 22)  
  (cidr (ip 198 32 12 0) 22)  
  (cidr (ip 198 32 154 0) 24)  
  (cidr (ip 198 71 45 0) 24)  
  (cidr (ip 198 71 46 0) 24)  
))

(define INDIANAGIGAPOP-PARTICIPANT (list
  (cidr (ip 65 254 96 0) 19)  
  (cidr (ip 65 254 96 0) 20)  
  (cidr (ip 66 205 160 0) 20)  
  (cidr (ip 66 254 224 0) 19)  
  (cidr (ip 72 12 215 0) 24)  
  (cidr (ip 108 59 48 0) 20)  
  (cidr (ip 128 10 0 0) 16)  
  (cidr (ip 128 46 0 0) 16)  
  (cidr (ip 128 210 0 0) 16)  
  (cidr (ip 128 211 0 0) 16)  
  (cidr (ip 128 252 0 0) 16)  
  (cidr (ip 129 74 0 0) 16)  
  (cidr (ip 129 79 0 0) 16)  
  (cidr (ip 134 68 0 0) 16)  
  (cidr (ip 136 165 0 0) 16)  
  (cidr (ip 140 182 0 0) 16)  
  (cidr (ip 140 182 44 192) 32)  
  (cidr (ip 140 221 223 0) 24)  
  (cidr (ip 149 159 0 0) 16)  
  (cidr (ip 149 160 0 0) 14)  
  (cidr (ip 149 160 0 0) 16)  
  (cidr (ip 149 161 0 0) 16)  
  (cidr (ip 149 162 0 0) 16)  
  (cidr (ip 149 163 0 0) 16)  
  (cidr (ip 149 164 0 0) 16)  
  (cidr (ip 149 165 0 0) 16)  
  (cidr (ip 149 165 182 0) 24)  
  (cidr (ip 149 166 0 0) 16)  
  (cidr (ip 150 131 0 0) 16)  
  (cidr (ip 156 56 0 0) 16)  
  (cidr (ip 157 91 0 0) 16)  
  (cidr (ip 159 242 0 0) 16)  
  (cidr (ip 161 32 0 0) 16)  
  (cidr (ip 162 244 104 0) 22)  
  (cidr (ip 162 244 108 0) 23)  
  (cidr (ip 165 134 0 0) 16)  
  (cidr (ip 192 12 206 0) 24)  
  (cidr (ip 192 73 48 0) 24)  
  (cidr (ip 192 88 99 0) 24)  
  (cidr (ip 192 195 225 0) 24)  
  (cidr (ip 192 195 226 0) 23)  
  (cidr (ip 192 195 228 0) 23)  
  (cidr (ip 192 195 230 0) 24)  
  (cidr (ip 192 195 234 0) 24)  
  (cidr (ip 192 195 248 0) 23)  
  (cidr (ip 192 195 250 0) 24)  
  (cidr (ip 192 207 124 0) 24)  
  (cidr (ip 192 231 192 0) 24)  
  (cidr (ip 192 245 116 0) 24)  
  (cidr (ip 199 120 154 0) 24)  
  (cidr (ip 204 52 32 0) 20)  
  (cidr (ip 205 137 32 0) 20)  
  (cidr (ip 207 196 129 0) 24)  
  (cidr (ip 207 196 132 0) 22)  
  (cidr (ip 207 196 136 0) 22)  
  (cidr (ip 207 196 140 0) 22)  
  (cidr (ip 207 196 144 0) 22)  
  (cidr (ip 207 196 148 0) 23)  
  (cidr (ip 207 196 153 0) 24)  
  (cidr (ip 207 196 154 0) 23)  
  (cidr (ip 207 196 156 0) 23)  
  (cidr (ip 207 196 158 0) 23)  
  (cidr (ip 207 196 167 0) 24)  
  (cidr (ip 207 196 168 0) 22)  
  (cidr (ip 207 196 172 0) 23)  
  (cidr (ip 207 196 174 0) 24)  
  (cidr (ip 207 196 175 0) 24)  
  (cidr (ip 207 196 176 0) 23)  
  (cidr (ip 207 196 178 0) 24)  
  (cidr (ip 207 196 180 0) 22)  
  (cidr (ip 207 196 184 0) 21)  
  (cidr (ip 207 196 192 0) 21)  
  (cidr (ip 207 196 200 0) 22)  
  (cidr (ip 207 196 204 0) 22)  
  (cidr (ip 216 162 48 0) 20)  
))

(define INDIANAGIGAPOP-SEGP (list
  (cidr (ip 12 159 195 0) 24)  
  (cidr (ip 12 159 206 0) 23)  
  (cidr (ip 12 159 209 0) 24)  
  (cidr (ip 69 51 160 0) 19)  
  (cidr (ip 76 78 1 0) 24)  
  (cidr (ip 131 93 0 0) 16)  
  (cidr (ip 137 112 0 0) 16)  
  (cidr (ip 139 102 0 0) 16)  
  (cidr (ip 147 53 0 0) 16)  
  (cidr (ip 147 226 0 0) 16)  
  (cidr (ip 152 228 0 0) 16)  
  (cidr (ip 157 91 0 0) 19)  
  (cidr (ip 157 91 48 0) 20)  
  (cidr (ip 157 91 64 0) 18)  
  (cidr (ip 157 91 128 0) 17)  
  (cidr (ip 159 28 0 0) 16)  
  (cidr (ip 159 218 0 0) 16)  
  (cidr (ip 159 242 0 0) 16)  
  (cidr (ip 161 32 0 0) 16)  
  (cidr (ip 163 120 0 0) 16)  
  (cidr (ip 163 245 0 0) 16)  
  (cidr (ip 165 138 0 0) 16)  
  (cidr (ip 165 139 0 0) 16)  
  (cidr (ip 167 217 0 0) 16)  
  (cidr (ip 168 91 0 0) 16)  
  (cidr (ip 168 102 0 0) 16)  
  (cidr (ip 192 146 191 0) 24)  
  (cidr (ip 192 146 192 0) 24)  
  (cidr (ip 192 189 3 0) 24)  
  (cidr (ip 192 195 225 0) 24)  
  (cidr (ip 192 195 226 0) 23)  
  (cidr (ip 192 195 228 0) 23)  
  (cidr (ip 192 195 230 0) 24)  
  (cidr (ip 192 200 128 0) 21)  
  (cidr (ip 192 206 9 0) 24)  
  (cidr (ip 192 206 10 0) 23)  
  (cidr (ip 192 207 174 0) 23)  
  (cidr (ip 192 207 176 0) 23)  
  (cidr (ip 192 207 178 0) 24)  
  (cidr (ip 198 51 243 0) 24)  
  (cidr (ip 198 51 244 0) 24)  
  (cidr (ip 198 62 84 0) 24)  
  (cidr (ip 198 62 98 0) 24)  
  (cidr (ip 199 8 0 0) 16)  
  (cidr (ip 204 52 48 0) 20)  
  (cidr (ip 205 215 64 0) 18)  
  (cidr (ip 208 96 144 0) 20)  
  (cidr (ip 208 119 0 0) 16)  
))

(define INDIANAGIGAPOP-SPONSORED (list
  (cidr (ip 149 165 251 0) 24)  
  (cidr (ip 216 88 164 0) 24)  
))

(define SANITY-OUT (list
  (term
    (list (as-path 'COMMERCIAL))
    (list (reject))
  )
  (term
    (list
      (route-filter (cidr (ip 0 0 0 0) 0) 'exact '())
      (route-filter (cidr (ip 10 0 0 0) 8) 'orlonger '())
      (route-filter (cidr (ip 127 0 0 0) 8) 'orlonger '())
      (route-filter (cidr (ip 169 254 0 0) 16) 'orlonger '())
      (route-filter (cidr (ip 172 16 0 0) 12) 'orlonger '())
      (route-filter (cidr (ip 192 0 2 0) 24) 'orlonger '())
      (route-filter (cidr (ip 192 88 99 1) 32) 'exact '())
      (route-filter (cidr (ip 192 168 0 0) 16) 'orlonger '())
      (route-filter (cidr (ip 198 18 0 0) 15) 'orlonger '())
      (route-filter (cidr (ip 224 0 0 0) 4) 'orlonger '())
      (route-filter (cidr (ip 240 0 0 0) 4) 'orlonger '())
    )
    (list (reject))
  )
  (term
    (list (community 'BLOCK-TO-EXTERNAL))
    (list (reject))
  )
))

(define REMOVE-COMMS-OUT (list
  (term
    '()
    (list
      (community-delete 'HIGH-PEERS)
      (community-delete 'LOW-PEERS)
      (community-delete 'LOW)
      (community-delete 'HIGH)
      (community-delete 'DISCARD)
    )
  )
))

(define ORIGINATE4 (list
  (term
    (list (community 'NLR-TELEPRESENCE))
    (list (reject))
  )
  (term
    (list (prefix-list INTERNAL))
    (list (accept))
  )
))

(define SANITY-IN (list
  (term
    (list (as-path 'PRIVATE))
    (list (reject))
  )
  (term
    (list (as-path 'COMMERCIAL))
    (list (reject))
  )
  (term
    (list (as-path 'NLR))
    (list (reject))
  )
  (term
    (list
     (route-filter (cidr (ip 0 0 0 0) 0) 'exact '())
     (route-filter (cidr (ip 10 0 0 0) 8) 'orlonger '())
     (route-filter (cidr (ip 127 0 0 0) 8) 'orlonger '())
     (route-filter (cidr (ip 169 254 0 0) 16) 'orlonger '())
     (route-filter (cidr (ip 172 16 0 0) 12) 'orlonger '())
     (route-filter (cidr (ip 192 0 2 0) 24) 'orlonger '())
     (route-filter (cidr (ip 192 88 99 1) 32) 'exact '())
     (route-filter (cidr (ip 192 168 0 0) 16) 'orlonger '())
     (route-filter (cidr (ip 198 18 0 0) 15) 'orlonger '())
     (route-filter (cidr (ip 224 0 0 0) 4) 'orlonger '())
     (route-filter (cidr (ip 240 0 0 0) 4) 'orlonger '())
    )
    (list (reject))
  )
  (term
    (list (prefix-list INTERNAL))
    (list (reject))
  )
))

(define SET-PREF (list
  (term
    (list (community 'HIGH))
    (list
      (local-preference 260)
      (next-policy)
    )
  )
  (term
    (list (community 'LOW))
    (list
      (local-preference 140)
      (next-policy)
    )
  )
  (term
    '()
    (list (local-preference 200))
  )
))

(define INTERNET2-MOSS (list
  (term
    (list (community 'INTERNET2-INFINERA))
    (list (accept))
  )
  (term
    '()
    (list (next-policy))
  )
))

(define INDIANAGIGAPOP-IN (list
  (term
    (list (prefix-list-filter INDIANAGIGAPOP-PARTICIPANT 'orlonger))
    (list (next-policy))
  )
  (term
    (list (prefix-list-filter INDIANAGIGAPOP-SEGP 'orlonger))
    (list
      (community-add 'SEGP)
      (next-policy)
    )
  )
  (term
    (list
      (prefix-list-filter INDIANAGIGAPOP-SPONSORED 'orlonger)
    )
    (list
      (community-add 'SPONSORED)
      (next-policy)
    )
  )
  (term
    '()
    (list (reject))
  )
))

(define CONNECTOR-IN (list
  (term
    '()
    (list
      (community-delete 'LOW-PEERS)
      (community-delete 'HIGH-PEERS)
      (next-term)
    )
  )
  (term
    (list
     (community 'DISCARD)
     (route-filter (cidr (ip 0 0 0 0) 0)
                   (prefix-length-range 24 32) '())
    )
    (list
      (community-add 'NO-EXPORT)
      (accept)
    )
  )
  (term
    (list
     (route-filter (cidr (ip 0 0 0 0) 0) (upto 27) '())
    )
    (list
      (community-add 'PARTICIPANT)
      (accept)
    )
  )
  (term
    (list
     (route-filter (cidr (ip 0 0 0 0) 0) (upto 27) '())
    )
    (list
      (community-add 'PARTICIPANT)
      (accept)
    )
  )
  (term
    '()
    (list (reject))
  )
))

(define ingp
  (neighbor   
    (ip 149 165 254 20) 'external
    (list SANITY-IN SET-PREF INTERNET2-MOSS INDIANAGIGAPOP-IN CONNECTOR-IN)   ; import
    (list SANITY-OUT REMOVE-COMMS-OUT ORIGINATE4)   ; export
  )
)

