#lang racket

(require redex
         rackunit)


(define-language Patina
  (prog ((sr ...) (fn ...)))
  ;; structures:
  (sr (struct s (l ...) ((f τ) ...)))
  ;; function def'ns
  (fn (fun g (l ...) ((x : τ) ...) bk))
  ;; blocks:
  (bk (block l (let (x : τ) ...) st ...))
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
      ()       ;; unit constant
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
     ()                   ;; ()
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
                      (let (v : ())
                        (u : (~ ()))
                        (p : (& a imm ())))
                      (v = ())
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
  ;; H (heap) : maps addresses to heap values
  [H ((alpha hv) ...)]
  ;; hv (heap values)
  [hv (ptr alpha) () (int number)]
  ;; V (vars) : a list of vmaps
  [V (vmap ...)]
  ;; vmap: maps variable names to addresses
  [vmap (((x alpha) ...) ...)]
  ;; T (types) : a list of tymaps
  [T (tymap ...)]
  ;; tymap : a map from names to types
  [tymap mt (((x ty) ...) ...)]
  ;; S (stack) : a list of 'ba's
  [S mt (ba S)]
  ;; ba (block activation) : a label and a list of statements
  [ba (l sts)]
  [sts mt (st sts)]
  [alpha number])


;; evaluate an rvalue, put the value at address alpha
(define-metafunction Patina-machine
  rv--> : prog H V T alpha rv -> (H V)
  ;; evaluate unit:
  [(rv--> prog (H ...) V T alpha ())
   (((alpha ()) H ...) V)]
  ;; ... and all the rest of the rules ...
  )

(redex-match Patina-machine H (term ((14 ()))))

(check-equal?
 (term (rv--> (() ()) () () () 14 ()))
 (term (((14 ())) ())))

(define machine-step
  (reduction-relation
   Patina-machine
   #;(--> (prog H V_1 (tymap T) ((l mt) S))
        ((free-some H tymap) (remove-vars V_2 V_1) T S)
        )
   (--> (prog H (vmap vmaps ...) 
              (tmap tmaps ...) ((l ((x = rv) st ...)) S))
        ()
        (where addr (alloc H ty))
        (where ty (type-of prog tmap x))
        (side-condition (not-in (term x) (term vmap)))
        )
   ))


(define-metafunction Patina-machine
  alloc : H ty -> alpha
  [(alloc H ty)
   ,(add1 (apply max (cons 0 (map car (term H)))))])

(check-equal? (term (alloc () int)) 1)
(check-equal? (term (alloc ((4 (ptr 2423)) (17 ())) int)) 18)


;; what's the type of this lval?
(define-metafunction Patina-machine
  type-of : prog tymap lv -> ty
  [(type-of prog (((x ty) rest ...) rest2 ...) x)
   ty]
  [(type-of prog (((x_1 ty_x) (x_2 ty_2) ...) tymap ...) x_3)
   (type-of prog (((x_2 ty_2) ...) tymap ...) x_3)]
  [(type-of prog (() (x_1 ty) ...) x)
   (type-of prog ((x_1 ty) ...) x)])

(redex-match Patina-machine tymap (term (((y int)(x ())))))
(check-equal?
 (term (type-of (() ()) (((y int)(x ()))) x))
 (term ()))


;; is x not in the vmap?
(define (not-in x vmap)
  (not (ormap (lambda (dict) (dict-ref dict x #f)) vmap)))

(check-equal?
 (not-in 'x '(((a 13) (b 14))
              ((z 3) (x 4))))
 #f)
(check-equal?
 (not-in 'x '(((a 13) (b 14))
              ((z 3) (o 4))))
 #t)

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


(check-true (and (redex-match Patina-machine H 
                              (term 
                               (49 22 (34 () mt))))
                 #t))



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
(check-false (term (tenv-contains? (x : () (lb ·)) la)))
(check-true (term (tenv-contains? (x : () (lb ·)) lb)))

(check-false (term (lifetime-<= la lb (x : () (y : () ·)))))
(check-true (term (lifetime-<= la lb (x : () (la (y : () (lb ·)))))))
;; is this as desired?
(check-true (term (lifetime-<= la la ·)))


(check-true (term (mq-< imm imm)))
(check-false (term (mq-< const imm)))


(check-true (term (subtype () () ·)))
(check-true (term (subtype (& l1 imm   (& l3 const ()))
                           (& l1 const (& l4 const ()))
                           (l4 (l3 ·)))))
(check-true (term (subtype (& l1 imm   (& l3 mut ()))
                           (& l1 const (& l4 mut ()))
                           (l4 (l3 ·)))))
(check-false (term (subtype (& l1 imm   (& l3 mut ()))
                           (& l1 const ())
                           (l4 (l3 ·)))))
(check-false (term (subtype (& l1 imm   (& l4 mut ()))
                            (& l1 const (& l3 mut ()))
                            (l4 (l3 ·)))))
(check-false (term (subtype (& l1 mut (& l3 const ()))
                           (& l1 mut (& l4 const ()))
                           (l4 (l3 ·)))))

(check-true
 (term (subtype (~ (& l1 imm (& l3 const ()))) 
                (~ (& l1 imm (& l4 const ())))
                (l4 (l3 ·)))))
(check-false
 (term (subtype (~ (& l1 imm (& l4 const ()))) 
                (~ (& l1 imm (& l3 const ())))
                (l4 (l3 ·)))))

(check-true 
 (term (subtype (struct-ty foo l1 l2 l3)
                (struct-ty foo l1 l2 l3)
                (l4 (l3 ·)))))

(check-false
 (term (subtype (struct-ty foo l1 l2 l3)
                (struct-ty foo l1 l4 l3)
                (l4 (l3 ·)))))

