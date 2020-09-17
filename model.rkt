#lang racket

(require redex)



(define-language
  layouts

  ; a layout
  [l :: l+ l× l⋅]
  
  [l+ ::= (+ l ...)] ; enum layout
  [l× ::= (× l ...)] ; struct layout
  [l⋅ ::= i u] ; atom layout

  ; initialized byte(s) in value range
  [i ::=
     (side-condition
      (init (name len natural)
            (name min natural)
            (name max natural))
      (< -1
         (term min)
         (term max)
         (expt 255 (term len))))]

  ; a type
  ; need to update this for the new `i` :/
  [t ::=
   (struct t ...)
   (union t ...)
   (array t natural)
   init
   foo]
  )

; enum syntactic sugar
; enum desugars to union of structs
#;
(define-metafunction layouts
  enum : (init_!_ (t ...)) ... -> t
  [(enum (init (t ...)) ...)
   (union (struct init t ...) ...)])

(define-metafunction layouts
  u8= : (side-condition (name value natural)
                        (<= 0 (term value) 255)) -> l⋅
  [(u8= natural)
   (init 1 natural ,(+ (term natural) 1))])

; align-of
(define-metafunction layouts
  align-of : t -> natural
  [(align-of foo)
   2]
  [(align-of init)
   1]
  [(align-of (array t natural))
   (align-of t)]
  [(align-of (struct t ...))
   ,(apply max (term ((align-of t) ...)))]
  [(align-of (union t ...))
   ,(apply max (term ((align-of t) ...)))])

; size-of
(define-metafunction layouts
  size-of : t -> natural
  [(size-of init)
   1]
  [(size-of foo)
   2]
  [(size-of (array t natural))
   ,(* (term (size-of t))
       (term natural))]
  [(size-of (struct t ...))
   ,(apply + (term ((size-of t) ...)))]
  [(size-of (union t ...))
   ,(apply max (term ((size-of t) ...)))])

(define (round-up-to-multiple offset align)
  (-
   (- (+ offset align) 1)
   (remainder (- (+ offset align) 1) align)
   offset))


(define-metafunction layouts
  layout-struct : natural number t ... -> l
  ; trailing padding
  [(layout-struct (name align natural) (name offset number))
   (+ ,@(make-list (round-up-to-multiple (term offset) (term align))
                   (term uninit)))]
  ; padding + field
  [(layout-struct (name struct-align natural) (name offset number) t t_rest ...)
   ,(let*
        ([align (term (align-of t))]
         [layout (term (layout-of t))]
         [offset (term offset)]
         [padding (round-up-to-multiple offset align)])
      (term
       (+ ,@(make-list padding (term uninit))
          ,layout
          (layout-struct
           struct-align
           ,(+ padding (term (size-of t)))
           t_rest ...))))])

(define-metafunction layouts
  layout-of : t -> l
  [(layout-of init)
   init]
  [(layout-of foo)
   42]
  [(layout-of (struct t ...))
   ,(let ([align (term (align-of (struct t ...)))])
      (term (layout-struct ,align 0 t ...)))])

; algebraic transformation of a term
(define-judgment-form layouts
  #:mode (~ I O)
  #:contract (~ l l)

  ; TODO more forms!

  ; right-associate +
  [(~ (+ l_0 l_1 l_2 l_n ...)
      (+ l_0 (+ l_1 l_2 l_n ...)))
   right-associate-+]

  ; right-associate ×
  [(~ (× l_0 l_1 l_2 l_n ...)
      (× l_0 (× l_1 l_2 l_n ...)))
   right-associate-×]

  ; left-distribute
  [(~ (× l_m (+ l_a ...))
      (+ (× l_a l_m) ...))
   left-distribute]
  
  ; right-distribute
  [(~ (× (+ l_a ...) l_m)
      (+ (× l_a l_m) ...))
   right-distribute]

  ; unwrap lone l from ×
  [(~ (× l)
      l)
   unwrap-×]

  ; unwrap lone l from +
  [(~ (+ l)
      l)
   unwrap-+]
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

  
  ; every variant of the src must be transmutable to dst
  [  (→ l_src l_dst) ...
   ------------------------ +→∗
   (→ (+ l_src ...) l_dst)]

  ; there must exist a variant of the dst such that the src
  ; is transmutable to that variant
  [        (→ l_src l_dst)
   -------------------------------- ∗→+
   (→ l_src (+ _ ... l_dst _ ...))]


  ; × → ×

  ; nom
  [(→ l_src l_dst) (→ (× l_src_n ...) (× l_dst_n ...))
   ---------------------------------------------------- +→+:nom
     (→ (× l_src l_src_n ...) (× l_dst l_dst_n ...))  ]

  ; bytes may be truncated from the `dst`; e.g.:
  ; union Transmute { src: u8, dst: () }
  [------------------- ×→×:shrink
   (→ (× l ...) (×)) ]

  ; uninit bytes may be conjure from the `src`; e.g.: 
  ; union Transmute { src: (), dst: u8 }
  [------------------------ ×→×:grow
   (→ (×) (× u ...)) ]


  ; ⋅ → ⋅
  [-------- init→init
   (→ i i)]

  [-------- init→uninit
   (→ i u)]

  [-------- uninit→uninit
   (→ u u)]
  )


(test-judgment-holds
 (→ (u8= 1) (u8= 1)))


; shrink
(test-judgment-holds
 (→ (× (u8= 1)) (×)))

; grow
(test-judgment-holds
 (→ (×) (× u)))

#;
(traces	
 ~
 (term (× (u8= 1) (u8= 2)))
 #:edge-labels? #t
 )


; nom
(test-judgment-holds
 (→ (× (u8= 1) (u8= 2)) (× (u8= 1) (u8= 2))))



(test-judgment-holds
 (→ (+ (× (u8= 1))) (+ (× (u8= 1)) (× (u8= 2)) (× (u8= 3)))))

(test-judgment-holds
 (→ (+ (× (u8= 2))) (+ (× (u8= 1)) (× (u8= 2)) (× (u8= 3)))))

(test-judgment-holds
 (→ (+ (× (u8= 3))) (+ (× (u8= 1)) (× (u8= 2)) (× (u8= 3)))))

; dist
(test-judgment-holds
 (→
  (+ (× (u8= 1) (u8= 3)) (× (u8= 2) (u8= 3)))
  (× (+ (u8= 1) (u8= 2)) (u8= 3))
 ))

; more dist
(test-judgment-holds
 (→
  (× (+ (u8= 1) (u8= 2)) (u8= 3) (u8= 4))
  (+ (× (u8= 1) (u8= 3) (u8= 4)) (× (u8= 2) (u8= 3) (u8= 4)))
 ))

#||#

(test-results)