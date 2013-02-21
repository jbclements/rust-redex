#lang racket

(require redex)


(define-language Patina
  (sr (struct s (l ...) ((fq f τ) ...)))
  (fn (fun g (l ...) ((x : τ) ...) bk))
  (bk (block l (let (x : τ) ...) st ...))
  (st (lv = rv) 
      (call g (l ...) (cm x) ...)
      bk)
  (lv x (o lv f) (* lv))
  (rv (cm x) 
      (lv o f)
      (* lv)
      (new s (l ...) (f cm x) ...)
      (~ cm x) 
      (& l mq lv)
      ())
  (cm copy move)
  (τ (struct-ty s (l ...))
     (~ τ)
     (& l mq τ)
     ())
  (τ+ τ
      (mq τ))
  (mq mut const imm)
  (fq mut e)
  (x variable-not-otherwise-mentioned)
  (g variable-not-otherwise-mentioned)
  (s variable-not-otherwise-mentioned)
  (l variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned)
  )

;; definition of REF is *totally buried* in the paper.
;; also, it looks like TYPE is currently implicit

;; paper should specify that 'imm' is default mutability
;; qualifier. Maybe it does?

;; bug: subtype for ~ includes mq, unlike defn of ty

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
                   (u = (~ copy v))))))




;; generate a random patina term
#;(generate-term Patina fn 5)


;; the subtype relation ; oh dear, it's parameterized
;; by lifetime inequality, and therefore by the program.
(define-relation
  Patina
  subtype ⊆ τ+ × τ+
  ;; subsumed by identity rule below:
  ;;[(subtype () ())]
  ;; my best guess at what the paper was supposed to say:
  [(subtype (~ τ+_1) (~ τ+_2))
   (subtype τ+_1 τ+_2)]
  ;; looks like maybe the struct rule should allow lifetimes
  ;; with a <= relationship?
  
  
  ;; I'm abbreviating, here. I think the paper should 
  ;; just use this:
  [(subtype τ τ)]
  )

;; testing the subtype relation
(require rackunit)
(check-true (term (subtype () ())))
(check-true (term (subtype (~ ()) (~ ()))))
(check-true
 (term (subtype (struct-ty a (l1 l2 l3))
                (struct-ty a (l1 l2 l3)))))
(check-false (term (subtype (struct-ty a (l1 l2 l3))
                            (struct-ty b (l1 l2 l3)))))



#;(define-extended-language Patina+Γ Patina
  [Γ · (x : τ Γ)])


#;(define-judgment-form
  Patina+Γ
  #:mode (fn-types )
  
  (define-judgment-form
  L+Γ
  #:mode (types I I O)
  #:contract (types Γ e t)
 
  [(types Γ e_1 (→ t_2 t_3))
   (types Γ e_2 t_2)
   -------------------------
   (types Γ (e_1 e_2) t_3)]
)
  
  )