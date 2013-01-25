#lang racket

(require redex)


(define-language Patina
  (sr (struct s (l ...) ((fq f ty) ...)))
  (fn (fun g (l ...) ((x : ty) ...) bk))
  (bk (block l (lets (x : ty) ...) st ...))
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
  (ty (struct-ty s (l ...))
      (~ ty)
      (& l mq ty)
      ())
  (mq mut const imm)
  (fq mut e)
  (x variable-not-otherwise-mentioned)
  (g variable-not-otherwise-mentioned)
  (s variable-not-otherwise-mentioned)
  (l variable-not-otherwise-mentioned)
  (f variable-not-otherwise-mentioned)
  )

;; definition of REF is *totally buried*.

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

(redex-match
 Patina fn
 (term (fun borrow () () 
            (block a
                   (lets (v : ())
                         (u : (~ ()))
                         (p : (& a imm ())))
                   (v = ())
                   (u = (~ copy v))
                   (p = (& z1 mut (* u)))
                   (u = (~ copy v))))))


#;(generate-term Patina fn 5)

(define-extended-language Patina+Γ Patina
  [Γ · (x : ty Γ)])


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