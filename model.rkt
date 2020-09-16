#lang racket

(require redex)

(define-language
  layouts

  [l ::=
     ; enums
     l+
     ; structs
     l×
     ; atoms
     l⋅]

  [l+ ::= (+ l ...)]
  [l× ::= (× l ...)]
  [l⋅ ::=
          ; initialized byte of value
          init
          ; uninitialized byte
          uninit]
          

  [init ::=
      (side-condition
       (name value number)
       (<= 0 (term value) 255))]

  [t ::=
   (struct t ...)
   (union t ...)
   (array t natural)
   init
   foo ; <- just here temporarily for testing types with alignment > 1]
  )

; enum syntactic sugar
; enum desugars to union of structs
(define-metafunction layouts
  enum : (init_!_ (t ...)) ... -> t
  [(enum (init (t ...)) ...)
   (union (struct init t ...) ...)])


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
  
  ; distribute
  [(~ (× (+ l_a ...) l_m)
      (+ (× l_a l_m) ...))]

  ; distribute
  [(~ (× l_m (+ l_a ...))
      (+ (× l_a l_m) ...))])

; is a layout transmutable to another layout?
(define-judgment-form layouts
  #:mode (→ I I)
  #:contract (→ l l)

  ; algebraic transformations of src and dst
  
  [ (~ l_src l_src′) (→ l_src′  l_dst)
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
   ---------------------------------------------------- ×→×:nom
     (→ (× l_src l_src_n ...) (× l_dst l_dst_n ...))  ]

  ; bytes may be truncated from the `dst`; e.g.:
  ; union Transmute { src: u8, dst: () }
  [------------------- ×→×:shrink
   (→ (× l ...) (×)) ]

  ; uninit bytes may be conjure from the `src`; e.g.: 
  ; union Transmute { src: (), dst: u8 }
  [------------------------ ×→×:grow
   (→ (×) (× uninit ...)) ]


  ; ⋅ → ⋅
  [-------------- init→init
   (→ init init)]

  [---------------- init→uninit
   (→ init uninit)]

  [------------------ uninit→uninit
   (→ uninit uninit)]


  
  

  
  )


(test-judgment-holds
 (→ 1 1))

; shrink
(test-judgment-holds
 (→ (× 1) (×)))
; grow
(test-judgment-holds
 (→ (×) (× uninit)))
; nom
(test-judgment-holds
 (→ (× 1 2) (× 1 2)))

(test-judgment-holds
 (→ (+ (× 1)) (+ (× 1) (× 2) (× 3))))

(test-judgment-holds
 (→ (+ (× 2)) (+ (× 1) (× 2) (× 3))))

(test-judgment-holds
 (→ (+ (× 3)) (+ (× 1) (× 2) (× 3))))

; dist
(test-judgment-holds
 (→
  (+ (× 1 3) (× 2 3))
  (× (+ 1 2) 3)
 ))

; dist (currently failing)
(test-judgment-holds
 (→
  (× (+ 1 2) 3 4)
  (+ (× 1 3 4) (× 2 3 4))
 ))



(test-results)