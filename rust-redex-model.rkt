#lang racket

(require redex
         rackunit)


(define-language Patina
  (prog ((sr ...) (fn ...)))
  ;; structures:
  (sr (struct s (l ...) ((f ty) ...)))
  ;; function def'ns
  (fn (fun g (l ...) ((x : ty) ...) bk))
  ;; blocks:
  (bk (block l (let (x : ty) ...) st ...))
  ;; statements:
  (st (lv = rv)
      (call g (l ...) (cm x) ...)
      (if0 rv bk bk)
      bk)
  ;; lvalues :
  (lv x (lv o f) (* lv))
  ;; rvalues :
  (rv (cm x)    ;; use of local variable
      (lv o f)  ;; field projection
      (* lv)    ;; dereference
      (new s (l ...) (f cm x) ...) ;; struct constant
      (~ cm x)  ;; create owned box
      (& l mq lv) ;; borrow
      unit       ;; unit constant
      ;; might be the easiest way to get turing-completeness?
      number  ;; constant number
      (+ rv rv) ;; sum
      )
  ;; copy/move :
  (cm copy move)
  ;; types : 
  (ty (struct-ty s l ...) ;; s<'l...>
     (~ ty)                 ;; ~t
     (& l mq ty)            ;; &'l mq t
     unit                   ;; unit
     int)
  ;; mq : mutability qualifier
  (mq mut const imm)
  ;; variables
  (x variable-not-otherwise-mentioned)
  ;; function names
  (g variable-not-otherwise-mentioned)
  ;; structure names
  (s variable-not-otherwise-mentioned)
  ;; labels
  (l variable-not-otherwise-mentioned)
  ;; field names
  (f variable-not-otherwise-mentioned)
  )


;; definition of REF is *totally buried* in the paper.
;; also, it looks like TYPE is currently implicit

;; paper should specify that 'imm' is default mutability
;; qualifier. Maybe it does?

#|
// example from fig. 7
// really unsure about the unspecified bits:
// - type of p: which mq?
// - p assignment: which mq?
// should simple lv be available as rv?
fn borrow() { a: {
let mut v: (), u: ~(), p: &a ();
v = ();
u = ~(copy v);
p = &*u; // ...until here, same as Fig. ?? 
u = ~(copy v); // invalidates p
} }|#

;; check that the example matches the grammar:
(check-not-exn
 (lambda ()
   (redex-match
    Patina fn
    (term (fun borrow () () 
               (block a
                      (let (v : unit)
                        (u : (~ unit))
                        (p : (& a imm unit)))
                      (v = unit)
                      (u = (~ copy v))
                      (p = (& z1 imm (* u)))
                      (u = (~ copy v))))))))




;; generate a random patina function
#;(generate-term Patina fn 5)

;;;;
;;
;; EVALUATION
;;
;;;;

(define-extended-language Patina-machine Patina
  ;; a configuration of the machine
  [configuration (prog H S)]
  ;; H (heap) : maps addresses to heap values
  [H ((alpha hv) ...)]
  ;; hv (heap values)
  [hv (ptr alpha) unit (int number)]
  ;; S (stack) : a stack of stack-frames
  [S done (sf S)]
  ;; sf (stack frame)
  [sf (vmap tmaps bas)]
  ;; vmap: maps variable names to addresses
  [vmap (((x alpha) ...) ...)]
  ;; tmaps : a map from names to types
  [tmaps (tmap ...)]
  [tmap ((x ty) ...)]
  ;; S (stack) : a list of block frames
  [bas mt (ba bas)]
  ;; ba (block activation) : a label and a list of statements
  [ba (l sts)]
  [sts mt (st sts)]
  [alpha number])


;; evaluate an rvalue, put the value at address alpha
(define-metafunction Patina-machine
  rv--> : prog H vmap tmaps alpha rv -> (H vmap)
  ;; evaluate unit:
  [(rv--> prog ((alpha_1 hv_1) ...) vmap tmaps alpha unit)
   (((alpha unit) (alpha_1 hv_1) ...) vmap)]
  ;; evaluate int:
  [(rv--> prog ((alpha_1 hv_1) ...) vmap tmaps alpha number)
   (((alpha (int number)) (alpha_1 hv_1) ...) vmap)]
  ;; ... and all the rest of the rules ...
  )

(check-equal?
 (term (rv--> (() ()) () () () 14 unit))
 (term (((14 unit)) ())))
(check-equal?
 (term (rv--> (() ()) ((9 (ptr 22))) () () 14 unit))
 (term (((14 unit) (9 (ptr 22))) ())))
(check-equal?
 (term (rv--> (() ()) ((9 (ptr 22))) () () 14 223))
 (term (((14 (int 223)) (9 (ptr 22))) ())))

(define machine-step
  (reduction-relation
   Patina-machine
   #;(--> (prog H V_1 (tmaps T) ((l mt) S))
        ((free-some H tmaps) (remove-vars V_2 V_1) T S)
        )
   ;; initialization of variable
   (--> (prog H ((vmap tmaps ((l ((x = rv) sts)) bas)) S))
        (prog H_1 ((vmap_2 tmaps ((l sts) bas)) S))
        ;; order matters, here:
        (side-condition (not (in-vmap (term x) (term vmap))))
        ;; actually unnecessary, if alloc doesn't take ty... :
        ;;; what's going on here?
        (where ty (type-of prog tmaps x))
        (where alpha (alloc H ty))
        (where (H_1 vmap_1)
               (rv--> prog H vmap tmaps alpha rv))
        (where vmap_2 (add-to-vmap x alpha vmap_1)))
   ;; fall-through...?
   (--> (prog H mt)
        ,(error (~a "finished evaluation"))
        )
   ))


(define-metafunction Patina-machine
  add-to-vmap : x alpha vmap -> vmap
  [(add-to-vmap x alpha 
                (((x_1 alpha_1) ...) ((x_2 alpha_2) ...) ...))
   (((x alpha) (x_1 alpha_1) ...) ((x_2 alpha_2) ...) ...)])

(check-equal? 
 (term (add-to-vmap frog 278 (((a 9)) () ((x 3) (y 4)))))
 (term (((frog 278) (a 9)) () ((x 3) (y 4)))))
;; the alloc metafunction returns the next unused slot.
(define-metafunction Patina-machine
  alloc : H ty -> alpha
  [(alloc H ty)
   ,(add1 (apply max (cons 0 (map car (term H)))))])

;; we'd like to prove a theorem that memory allocations 
;; can't overlap... actually, there are a whole bunch of 
;; theorems here.

(check-equal? (term (alloc () int)) 1)
(check-equal? (term (alloc ((4 (ptr 2423)) (17 unit)) int)) 18)


;; what's the type of this lval?
(define-metafunction Patina-machine
  type-of : prog tmaps lv -> ty
  [(type-of prog (((x ty) (x_dc ty_dc) ...) tmap ...) x)
   ty]
  [(type-of prog (((x_1 ty_x) (x_2 ty_2) ...) tmap ...) x_3)
   (type-of prog (((x_2 ty_2) ...) tmap ...) x_3)]
  [(type-of prog (() (x_1 ty) ...) x)
   (type-of prog ((x_1 ty) ...) x)])

(check-equal?
 (term (type-of (() ()) (((y int)(x unit))) x))
 (term unit))

(check-equal?
 (term (type-of (() ()) (((f unit) (g int))) f))
 (term unit))

;; is x in the vmap?
(define (in-vmap x vmap)
  (and (ormap (lambda (dict) (dict-ref dict x #f)) vmap)
       #t))

(check-equal?
 (in-vmap 'x '(((a 13) (b 14))
              ((z 3) (x 4))))
 #t)
(check-equal?
 (in-vmap 'x '(((a 13) (b 14))
              ((z 3) (o 4))))
 #f)

;; we can take a single step!
(let ()
  (define prog (term (() ())))
  (define tmaps (term (((f unit) (g int)))))
  (test--> machine-step
           (term (,prog () ; heap
                        (((()) ,tmaps ((l1 ((f = unit) mt)) mt)) done)))
           (term (,prog ((1 unit)); heap
                        (((((f 1))) 
                          ,tmaps 
                          ((l1 mt) mt)) done))))
  ;; we can violate the type system, too...
  (test--> machine-step
           (term (,prog () ; heap
                        (((()) ,tmaps ((l1 ((f = 99) mt)) mt)) done)))
           (term (,prog ((1 (int 99))); heap
                        (((((f 1))) 
                          ,tmaps 
                          ((l1 mt) mt)) done))))
  ;; two steps
  (test-->> machine-step
           (term (,prog () ; heap
                        (((()) ,tmaps ((l1 ((f = unit)
                                           ((g = 14)
                                            mt))) mt)) done)))
           (term (,prog ((2 (int 14)) (1 unit)); heap
                        (((((g 2) (f 1))) 
                          ,tmaps 
                          ((l1 mt) mt)) done))))
  ;; mutating an existing value
  )

;; 

;; stub function
(define-metafunction Patina-machine
  free-some : H V -> H
  ;; ... clauses here
  )

;; stub function
;; remove the variables mentioned in V_1 from V_2
(define-metafunction Patina-machine
  remove-vars : V V -> V
  ;; ... clauses here
  )


;; load a program as a configuration
;; 
#;(define (load prog))



;; multiplication. destroys a, sorry. Can't wait until this runs....
(term
 (fun mult () ((a : (& l1 mut int)) 
               (b : (& l2 const int))
               (sum : (& l3 mut int)))
      (block l4 (let) 
             (if0 (* a)
                  (block l5 (let))
                  (block l6 (let)
                         ((* sum) = (+ (* b) (* sum)))
                         ((* a) = (+ -1 (* a)))
                         (call mult (move a) (move b) (move c)))))))


;;;;
;;
;; TYPE CHECKING
;;
;;;;

(define-extended-language Patina+Γ Patina
  [Γ · 
     (x : ty Γ)
     (l Γ)])




;; the subtype relation
(define-relation
  Patina+Γ
  subtype ⊆ ty × ty × Γ
  ;; implied by written rules (by induction on 
  ;; structure of types), subsumes several rules.
  [(subtype ty ty Γ)]
  [(subtype (& l_1 mq_1 ty_1) (& l_2 mq_2 ty_2) Γ)
   ;; contravariant in lifetimes
   (lifetime-<= l_2 l_1 Γ)
   ;; relation extracted from type rules:
   (mq-< mq_1 mq_2)
   (subtype ty_1 ty_2 Γ)]
  ;; special-case for mut: NB types are the same
  [(subtype (& l_1 mut ty) (& l_2 mut ty) Γ)
   ;; contravariant in lifetimes
   (lifetime-<= l_2 l_1 Γ)]
  [(subtype (~ ty_1) (~ ty_2) Γ)
   (subtype ty_1 ty_2 Γ)]
  )

;; an abstraction for the & rule
(define-relation
  Patina+Γ
  mq-< ⊆ mq × mq
  ;; anything is less than const
  [(mq-< mq const)]
  ;; imm is <= imm
  [(mq-< imm imm)]
  )

;; does l1 occur before l2 in the tenv or are they equal?
(define-relation
  Patina+Γ
  lifetime-<= ⊆ l × l × Γ
  ;; it might be more consistent to insist that it appears somewhere...
  [(lifetime-<= l_1 l_1 Γ)]
  [(lifetime-<= l_1 l_2 (x : ty Γ))
   (lifetime-<= l_1 l_2 Γ)]
  ;; l_1 < l_2 if l_1 is inside l_2, right?
  [(lifetime-<= l_1 l_2 (l_1 Γ))
   (tenv-contains? Γ l_2)])

;; does the type environment contain the lifetime l?
(define-relation
  Patina+Γ  
  tenv-contains? ⊆ Γ × l
  [(tenv-contains? (x : ty Γ) l)
   (tenv-contains? Γ l)]
  [(tenv-contains? (l Γ) l)])


;; it should be possible to make this work somehow...
#;(generate-term #:source bogo 5)

(check-false (term (tenv-contains? · la)))
(check-false (term (tenv-contains? (x : unit (lb ·)) la)))
(check-true (term (tenv-contains? (x : unit (lb ·)) lb)))

(check-false (term (lifetime-<= la lb (x : unit (y : unit ·)))))
(check-true (term (lifetime-<= la lb (x : unit (la (y : unit (lb ·)))))))
;; is this as desired?
(check-true (term (lifetime-<= la la ·)))


(check-true (term (mq-< imm imm)))
(check-false (term (mq-< const imm)))


(check-true (term (subtype unit unit ·)))
(check-true (term (subtype (& l1 imm   (& l3 const unit))
                           (& l1 const (& l4 const unit))
                           (l4 (l3 ·)))))
(check-true (term (subtype (& l1 imm   (& l3 mut unit))
                           (& l1 const (& l4 mut unit))
                           (l4 (l3 ·)))))
(check-false (term (subtype (& l1 imm   (& l3 mut unit))
                           (& l1 const unit)
                           (l4 (l3 ·)))))
(check-false (term (subtype (& l1 imm   (& l4 mut unit))
                            (& l1 const (& l3 mut unit))
                            (l4 (l3 ·)))))
(check-false (term (subtype (& l1 mut (& l3 const unit))
                           (& l1 mut (& l4 const unit))
                           (l4 (l3 ·)))))

(check-true
 (term (subtype (~ (& l1 imm (& l3 const unit))) 
                (~ (& l1 imm (& l4 const unit)))
                (l4 (l3 ·)))))
(check-false
 (term (subtype (~ (& l1 imm (& l4 const unit))) 
                (~ (& l1 imm (& l3 const unit)))
                (l4 (l3 ·)))))

(check-true 
 (term (subtype (struct-ty foo l1 l2 l3)
                (struct-ty foo l1 l2 l3)
                (l4 (l3 ·)))))

(check-false
 (term (subtype (struct-ty foo l1 l2 l3)
                (struct-ty foo l1 l4 l3)
                (l4 (l3 ·)))))

