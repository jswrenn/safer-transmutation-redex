#lang racket
(require redex)

(define-language
  layouts

  [l ::=
     ; unions
     l+

     ; structs
     l×

     ; atoms
     la]

  [l+ ::= (+ l l)]
  [l× ::= (× l l)]
  [la ::=
      ; zst
      ε

      ; void
      ∅

      lb]

  [lb ::=
      ; uninit bytes
      (u (name len natural))
      
      ; init bytes with valid range
      (side-condition
       (i (name len natural)
          (name min natural)
          (name max natural))
       (< -1
          (term min)
          (term max)
          (expt 255 (term len))))]
  )

; add two numbers
(define-metafunction layouts
  ⊕ : natural natural -> natural
  [(⊕ natural_0 natural_1)
   ,(+ (term natural_0) (term natural_1))])

; saturating sub
(define-metafunction layouts
  ⊖ : natural natural -> natural
  [(⊖ natural_0 natural_1)
   ,(min 0 (- (term natural_0) (term natural_1)))])

; integer divide
(define-metafunction layouts
  ⊘ : natural natural -> natural
  [(⊘ natural_0 natural_1)
   ,(quotient (term natural_0) (term natural_1))])

; max
(define-metafunction layouts
  ⊔ : natural natural -> natural
  [(⊔ natural_0 natural_1)
   ,(max (term natural_0) (term natural_1))])

; min
(define-metafunction layouts
  ⊓ : natural natural -> natural
  [(⊓ natural_0 natural_1)
   ,(min (term natural_0) (term natural_1))])

; exponentiation
(define-metafunction layouts
  ^ : natural natural -> natural
  [(^ natural_0 natural_1)
   ,(expt (term natural_0) (term natural_1))])

; len of an `i` or `u` byte sequence
(define-metafunction layouts
  📏 : lb -> natural_len
  [(📏 (u natural_len))
   natural_len]

  [(📏 (i natural_len natural_min natural_max))
   natural_len])

; neq
(define-metafunction layouts
  ≠ : natural natural -> boolean
  [(≠ natural natural) #f]
  [(≠ natural_0 natural_1) #t])
; eq
(define-metafunction layouts
  = : natural natural -> boolean
  [(= natural natural) #t]
  [(= natural_0 natural_1) #f])
; lte
(define-metafunction layouts
  ≤ : natural natural -> boolean
  [(≤ natural_0 natural_1)
   ,(<= (term natural_0) (term natural_1))])
; gte
(define-metafunction layouts
  ≥ : natural natural -> boolean
  [(≥ natural_0 natural_1)
   ,(>= (term natural_0) (term natural_1))])

; snip bytes
; todo: test this! I just eyeballed it.
(define-metafunction layouts
  ✂ : lb natural -> (lb lb)
  [(✂ (u natural_len) natural_snip)
   ((u (⊓ natural_len natural_snip))
    (u (⊖ natural_len natural_snip)))]

  ; this is the routine for little-endian targets
  [(✂ (i natural_len natural_min natural_max) natural_snip)
   ((i natural_snip
       (⊓ natural_len natural_snip)
       (⊓ natural_min (^ 2 (⊓ natural_len natural_snip)))
       (⊓ natural_max (^ 2 (⊓ natural_len natural_snip))))
    (i (⊖ natural_len natural_snip)
       (⊘ (⊔ natural_min (^ 2 (⊖ natural_len natural_snip))))
       (⊘ natural_max (^ 2 (⊖ natural_len natural_snip)))))])

; append
(define-metafunction layouts
  ⧺ : l l -> l

  ; (⧺ × l)
  [(⧺ (× l_0 l_1) l_2)
   (× l_0 (⧺ l_1 l_2))]

  ; (⧺ + l)
  [(⧺ (+ l_0 l_1) l_2)
   (+ (⧺ l_0 l_2)
      (⧺ l_1 l_2))]

  ; (⧺ a l)
  [(⧺ la l)
   (× la l)]
  )

; simplify a term
(define-judgment-form layouts
  #:mode (~ I O)
  #:contract (~ l l)

  ; reassociate
  [(~ (× l_0 l_1)
      (⧺ l_0 l_1))
   reassociate]
  
  ; left-distribute
  [(~ (× l_m (+ l_a0 l_a1))
      (+ (× l_m l_a0) (× l_m l_a1)))
   left-distribute]

  ; right-distribute
  [(~ (× (+ l_a0 l_a1) l_m)
      (+ (× l_a0 l_m) (× l_a1 l_m)))
   right-distribute]

  ; eliminate ε from ×
  [(~ (× l ε) l) unwrap-×-l]
  [(~ (× ε l) l) unwrap-×-r]

  ; eliminate empty bytes
  ; u~ε
  [(~ (u 0)
      ε)
   u~ε]
  ; i~ε
  [(~ (i 0 _ _)
      ε)
   i~ε]

  )

; is a layout transmutable to another layout?
(define-judgment-form layouts
  #:mode (→ I I)
  #:contract (→ l l)

  ; algebraic transformations of src and dst
  [ (~ l_src l_src′) (→ l_src′ l_dst)
   ----------------------------------- src′
            (→ l_src l_dst)          ]
  
  [ (~ l_dst l_dst′) (→ l_src  l_dst′)
   ----------------------------------- dst′
            (→ l_src l_dst)          ]
  
  ;; +→∗
  ; 1. +→×
  ; 2. +→a
  ; 3. +→+

  ; every variant of the src must be transmutable to dst
  [(→ l_src_0 l_dst) (→ l_src_1 l_dst)
   ----------------------------------- +→∗
     (→ (+ l_src_0 l_src_1) l_dst)   ]

  
  ;; ∗→+
  ; 3. +→+
  ; 4. a→+
  ; 5. ×→+

  ; src is transmutable to the left variant of dst
  [      (→ l_src l_dst_0)
   ------------------------------ ∗→+-L
   (→ l_src (+ l_dst_0 l_dst_1))]

  ; src is transmutable to the right variant of dst
  [      (→ l_src l_dst_1)
   ------------------------------ ∗→+-R
   (→ l_src (+ l_dst_0 l_dst_1))]


  
  ;; 6. ×→×
  ; the cases where the first operand of ×
  ; isn't an atom are handled by ~
  [     (⇝ la_src la_dst la_src′ la_dst′)
    (→ (× la_src′ l_src) (× la_dst′ l_dst))
   ----------------------------------------- ×→×
     (→ (× la_src l_src) (× la_dst l_dst)) ]

  ;; 7. ×→a
  [(⇝ la_src la_dst la_src′ la_dst′)
     (→ (× la_src′ l_src) la_dst′)
   --------------------------------- ×→a
     (→ (× la_src l_src) la_dst)   ]

  ;; 8. a→×
  [(⇝ la_src la_dst la_src′ la_dst′)
     (→ la_src′ (× la_dst′ l_dst))
   --------------------------------- a→×
     (→ la_src (× la_dst l_dst))   ]

  ;; 9. a→a
  [(⇝ la_src la_dst la_src′ la_dst′)
          (→ la_src′ la_dst′)
   --------------------------------- a→a
           (→ la_src la_dst)       ]
  
  )

; nom
; ⇝ consumes a src atom and dst atom,
; chomps as much as possible off src and dst
; and produces their remainders
(define-judgment-form layouts
  #:mode (⇝ I I O O)
  #:contract (⇝ la la la la)

  ; ∅ is transmutable into everything
  ; fine since ∅ isn't constructible
  [(⇝ ∅ l
      ε l)]

  ; b→b; with length-equalizing snip
  [(side-condition
    (≠ (📏 lb_src)
       (📏 lb_dst)))
   
   (where (lb_src′ lb_src″)
          (✂ lb_src))

   (where (lb_dst′ lb_dst″)
          (✂ lb_dst))

   (→ lb_src′ lb_dst′)
   ----------------------------------
   (⇝ lb_src lb_dst lb_src″ lb_dst″)]

  ; b→b; without length-equalizing snip
  [(side-condition
    (= (📏 lb_src)
       (📏 lb_dst)))
   
   (→ lb_src lb_dst)
   ----------------------
   (⇝ lb_src lb_dst ε ε)]
  )

(define-judgment-form layouts
  #:mode (⊆ I I)
  #:contract (⊆ lb lb)

  [(⊆ (u natural_len)
      (u natural_len))]

  [(⊆ (i natural_len
         natural_min
         natural_max)
      (u natural_len))]

  [(side-condition
    (≥ natural_src_min natural_dst_min))
   (side-condition
    (≤ natural_src_max natural_dst_max))
   -------------------------------------
   (⊆ (i natural_len
         natural_src_min
         natural_src_max)
      (i natural_len
         natural_dst_min
         natural_dst_max))])

; shorthand for test cases
(define-metafunction layouts
  u8 : (side-condition (name value natural)
                       (<= 0 (term value) 255)) -> l⋅
  [(u8 natural)
   (init 1 natural ,(+ (term natural) 1))])
