#lang racket

(require redex
         rackunit)

(define-language Patina
  (prog (srs (fn ...)))
  ;; structures:
  (srs (sr ...))
  (sr (struct s ls (ty ...)))
  ;; lifetimes:
  (ls (l ...))
  ;; function def'ns
  (fn (fun g ls ((x : ty) ...) bk))
  ;; blocks:
  (bk (block l (let (x : ty) ...) st ...))
  ;; statements:
  (st (lv = rv)
      (call g (l ...) (cm x) ...)
      (if0 x bk bk)
      (drop lv)
      bk)
  ;; lvalues :
  ;; changing "field names" to be numbers
  (lvs (lv ...))
  (lv x (lv : f) (* lv))
  ;; rvalues :
  (rv (cm lv)                      ;; copy lvalue
      (& l mq lv)                  ;; take address of lvalue
      (struct s ls (lv ...))       ;; struct constant
      (new lv)                     ;; allocate memory
      number                       ;; constant number
      (+ lv lv)                    ;; sum
      )
  (cm copy move)
  ;; types : 
  (tys (ty ...))
  (ty (struct-ty s ls)             ;; s<'l...>
      (~ ty)                       ;; ~t
      (& l mq ty)                  ;; &'l mq t
      int)                         ;; int
  ;; mq : mutability qualifier
  (mq mut imm)
  ;; variables
  (x variable-not-otherwise-mentioned)
  ;; function names
  (g variable-not-otherwise-mentioned)
  ;; structure names
  (s variable-not-otherwise-mentioned)
  ;; labels
  (l variable-not-otherwise-mentioned)
  ;; field "names"
  (f number)
  )

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
  [hv (ptr alpha) (int number)]
  ;; S (stack) : a stack of stack-frames
  [S (sf ...)]
  ;; sf (stack frame)
  [sf (V T bas)]
  ;; V: maps variable names to addresses
  [V (vmap ...)]
  [vmap ((x alpha) ...)]
  ;; T : a map from names to types
  [T (tmap ...)]
  [tmap ((x ty) ...)]
  ;; ba (block activation) : a label and a list of statements
  [bas (ba ...)]
  [ba (l sts)]
  [sts (st ...)]
  [(alphas betas gammas) (number ...)]
  [(alpha beta gamma) number]
  ;; z -- sizes, offsets
  [zs (z ...)]
  [z number])

;; unit test setup for helper fns

(define test-srs
  (term [(struct A () (int))
         (struct B (l0) (int (& l0 mut int)))
         (struct C (l0) ((struct-ty A ())
                         (struct-ty B (l0))))
         (struct D (l0) ((struct-ty C (l0))
                         (struct-ty A ())
                         (struct-ty C (l0))
                         (struct-ty B (l0))))
         ]))

(define test-T (term (((i int)
                       (p (~ int)))
                      ((a (struct-ty A ()))
                       (b (struct-ty B (static)))
                       (c (struct-ty C (static)))))))

(define test-V (term (((i 10)
                       (p 11))
                      ((a 12)
                       (b 13)
                       (c 15)))))

(define test-H (term [(10 (int 22)) ;; i == 22
                      (11 (ptr 99)) ;; p == 99
                      (12 (int 23)) ;; a:0
                      (13 (int 24)) ;; b:0
                      (14 (ptr 98)) ;; b:1
                      (15 (int 25)) ;; c:1:0
                      (16 (int 26)) ;; c:1:0
                      (17 (ptr 97)) ;; c:1:1
                      (97 (int 27))   ;; *c:1:1
                      (98 (int 28))   ;; *b:1
                      (99 (int 28))])) ;; *p

;; get -- a version of assoc that works on lists like '((k v) (k1 v1))

(define (get key list)
  (cadr (assoc key list)))

(define (get* key lists)
  (let ([v (assoc key (car lists))])
    (if (not v)
        (get* key (cdr lists))
        (cadr v))))

(test-equal (get* (term a) (term (((a 1) (b 2)) ((c 3)))))
            1)

(test-equal (get* (term c) (term (((a 1) (b 2)) ((c 3)))))
            3)

(test-equal (get* (term e) (term (((a 1) (b 2)) ((c 3)) ((d 4) (e 5)))))
            5)

;; prefix sum

(define-metafunction Patina-machine
  prefix-sum : z zs -> zs
  
  [(prefix-sum z_0 ()) ()]
  [(prefix-sum z_0 (z_1 z_2 ...))
   ,(append (term (z_3)) (term (prefix-sum z_3 (z_2 ...))))
   (where z_3 ,(+ (term z_0) (term z_1)))])

(test-equal (term (prefix-sum 0 ()))
            (term ()))

(test-equal (term (prefix-sum 0 (1 2 3)))
            (term (1 3 6)))

;; deref function -- search a heap for a given address.

(define-metafunction Patina-machine
  deref : H alpha -> hv

  [(deref H alpha)
   ,(get (term alpha) (term H))])

(test-equal (term (deref [(1 (ptr 22))] 1)) (term (ptr 22)))
(test-equal (term (deref [(2 (ptr 23)) (1 (int 22))] 1)) (term (int 22)))

;; update -- replaces value for alpha

(define-metafunction Patina-machine
  update : H alpha hv -> H
  
  [(update ((alpha_0 hv_0) (alpha_1 hv_1) ...) alpha_0 hv_2)
   ((alpha_0 hv_2) (alpha_1 hv_1) ...)]

  [(update ((alpha_0 hv_0) (alpha_1 hv_1) ...) alpha_2 hv_2)
   ,(append (term ((alpha_0 hv_0))) (term (update ((alpha_1 hv_1) ...) alpha_2 hv_2)))])

(test-equal (term (update [(2 (ptr 23)) (1 (int 22))] 1 (int 23)))
            (term ((2 (ptr 23)) (1 (int 23)))))

(test-equal (term (update [(2 (ptr 23)) (1 (int 22))] 2 (int 23)))
            (term ((2 (int 23)) (1 (int 22)))))

;; memcopy -- copies memory from one address to another

(define-metafunction Patina-machine
  memcopy : H alpha beta number -> H
  
  [(memcopy H alpha beta 0) H]

  [(memcopy H alpha beta number)
   (memcopy (update H alpha (deref H beta))
            ,(add1 (term alpha))
            ,(add1 (term beta))
            ,(sub1 (term number)))])

(test-equal (term (memcopy [(10 (ptr 1))
                            (11 (int 2))
                            (12 (ptr 3))
                            (20 (ptr 4))
                            (21 (int 5))
                            (22 (ptr 6))]
                           20
                           10
                           3))
            (term [(10 (ptr 1))
                   (11 (int 2))
                   (12 (ptr 3))
                   (20 (ptr 1))
                   (21 (int 2))
                   (22 (ptr 3))]))

(test-equal (term (update [(2 (ptr 23)) (1 (int 22))] 2 (int 23)))
            (term ((2 (int 23)) (1 (int 22)))))

;; vaddr -- lookup addr of variable in V
 
(define-metafunction Patina-machine
  vaddr : V x -> alpha
  
  [(vaddr V x_0)
   ,(get* (term x_0) (term V))])
         
(test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) a))
            (term 0))
(test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) b))
            (term 1))
(test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) c))
            (term 2))

;; vtype -- lookup type of variable in V
 
(define-metafunction Patina-machine
  vtype : T x -> ty
  
  [(vtype T x_0)
   ,(get* (term x_0) (term T))])

(test-equal (term (vtype ,test-T i)) (term int))

(test-equal (term (vtype ,test-T c)) (term (struct-ty C (static))))

;; struct-tys

(define-metafunction Patina-machine
  struct-tys : srs s ls -> (ty ...)
  
  [(struct-tys ((struct s_0 (l_0 ...) (ty_0 ...)) sr ...) s_0 ls_1)
   (ty_0 ...)] ;; XXX subst lifetimes

  [(struct-tys ((struct s_0 (l_0 ...) (ty_0 ...)) sr ...) s_1 ls_1)
   (struct-tys (sr ...) s_1 ls_1)])

(test-equal (term (struct-tys ,test-srs A ()))
            (term (int)))

;; sizeof

(define-metafunction Patina-machine
  sizeof : srs ty -> number
  
  [(sizeof srs int) 
   1]
  
  [(sizeof srs (~ ty))
   1]
  
  [(sizeof srs (& l mq ty))
   1]
  
  [(sizeof srs (struct-ty s ls))
   ,(foldl + 0 (map (lambda (t) (term (sizeof srs ,t)))
                    (term (struct-tys srs s ls))))]) 

(test-equal (term (sizeof ,test-srs (struct-ty A ())))
            (term 1))

(test-equal (term (sizeof ,test-srs (struct-ty B (static))))
            (term 2))

(test-equal (term (sizeof ,test-srs (struct-ty C (static))))
            (term 3))

;; offsets -- determines the offsets of each field of a struct

(define-metafunction Patina-machine
  offsets : srs s ls -> zs
  
  [(offsets srs s ls)
   ,(append '(0) (term (prefix-sum 0 zs)))
   (where tys (struct-tys srs s ls))
   (where zs ,(drop-right (map (lambda (t) (term (sizeof srs ,t)))
                               (term tys)) 1))])

(test-equal (term (offsets ,test-srs C (static)))
            (term (0 1)))

;; offsetof

(define-metafunction Patina-machine
  offsetof : srs s ls f -> z
  
  [(offsetof srs s ls f)
   ,(foldl + 0 (map (lambda (t) (term (sizeof srs ,t)))
                    (take (term (struct-tys srs s ls))
                          (term f))))])

(test-equal (term (offsetof ,test-srs C (static) 0))
            (term 0))

(test-equal (term (offsetof ,test-srs C (static) 1))
            (term 1))

(test-equal (term (offsetof ,test-srs D (static) 1))
            (term 3))

(test-equal (term (offsetof ,test-srs D (static) 3))
            (term 7))

;; lvtype -- compute type of an lvalue

(define-metafunction Patina-machine
  dereftype : ty -> ty
  
  [(dereftype (~ ty)) ty]
  [(dereftype (& l mq ty)) ty])

(define-metafunction Patina-machine
  fieldtype : srs ty f -> ty
  
  [(fieldtype srs (struct-ty s ls) f)
   ,(car (drop (term (struct-tys srs s ls)) (term f)))]) ; fixme--surely a better way

(define-metafunction Patina-machine
  lvtype : srs T lv -> ty
  
  [(lvtype srs T x)
   (vtype T x)]
  
  [(lvtype srs T (* lv))
   (dereftype (lvtype srs T lv))]
  
  [(lvtype srs T (lv : f))
   (fieldtype srs (lvtype srs T lv) f)])

(test-equal (term (lvtype ,test-srs ,test-T (* p))) (term int))

;; FIXME --> l0 should be static
(test-equal (term (lvtype ,test-srs ,test-T (c : 1))) (term (struct-ty B (l0))))

;; lvaddr -- lookup addr of variable in V

(define-metafunction Patina-machine
  lvaddr : srs H V T lv -> alpha
  
  [(lvaddr srs H V T x)
   (vaddr V x)]
  
  [(lvaddr srs H V T (* lv))
   alpha
   (where (ptr alpha) (deref H (lvaddr srs H V T lv)))]
       
  [(lvaddr srs H V T (lv : f))
   ,(+ (term (lvaddr srs H V T lv))
       (term (offsetof srs s ls f)))
   (where (struct-ty s ls) (lvtype srs T lv))])

(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (c : 1)))
            (term 16))

(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T ((c : 1) : 1)))
            (term 17))

(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (* ((c : 1) : 1))))
            (term 97))

;; malloc -- return an unused address with sufficient space for z entries

(define-metafunction Patina-machine
  malloc : H z -> alpha

  [(malloc H z)
   alpha
   (where alphas ,(map car (term H)))
   (where alpha ,(add1 (apply max (term alphas))))])

(test-equal (term (malloc ,test-H 100))
            (term 100))

;; rveval -- evaluate an rvalue and store it into the heap at address alpha

(define-metafunction Patina-machine
  copyfields : H zs alphas betas -> H

  [(copyfields H () () ())
   H]

  [(copyfields H (z_0 z_1 ...) (alpha_0 alpha_1 ...) (beta_0 beta_1 ...))
   (copyfields (memcopy H alpha_0 beta_0 z_0)
               (z_1 ...)
               (alpha_1 ...)
               (beta_1 ...))])

(define-metafunction Patina-machine
  rveval : srs H V T alpha rv -> H

  [(rveval srs H V T alpha (cm lv))
   H_1
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where beta (lvaddr srs H V T lv))
   (where H_1 (memcopy H alpha beta z))]

  [(rveval srs H V T alpha (& l mq lv))
   H_1
   (where beta (lvaddr srs H V T lv))
   (where H_1 (update H alpha (ptr beta)))]

  [(rveval srs H V T alpha (struct s ls lvs))
   (copyfields H zs_0 betas alphas)

   ;; types of each field:
   (where tys (struct-tys srs s ls))
   ;; sizes of each field's type:
   (where zs_0 ,(map (lambda (t) (term (sizeof srs ,t))) (term tys)))
   ;; offset of each field:
   (where zs_1 (offsets srs s lvs))
   ;; source address of value for each field:
   (where alphas ,(map (lambda (lv) (term (lvaddr srs H V T ,lv))) (term lvs)))
   ;; target address for each field relative to base address alpha;
   (where betas ,(map (lambda (z) (+ (term alpha) z)) (term zs_1)))]

  [(rveval srs H V T alpha (new lv))
   (update H_1 alpha (ptr gamma))

   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where beta (lvaddr srs H V T lv))
   (where gamma (malloc H z))
   (where H_1 (memcopy H gamma beta z))]
   
  [(rveval srs H V T alpha number)
   (update H_1 alpha (int number))]
   
  [(rveval srs H V T alpha (+ lv_0 lv_1))
   (update H alpha (int number_2))

   (where beta (lvaddr srs H V T lv))
   (where gamma (lvaddr srs H V T lv))
   (where (int number_0) (deref H beta))
   (where (int number_1) (deref H gamma))
   (where number_2 ,(+ (term number_0) (term number_1)))])

;; lvselect -- helper for writing tests, selects values for a portion
;; of the heap

(define (select H alpha z)
  (let* [(matching (filter (lambda (pair) (and (>= (car pair) alpha)
                                               (< (car pair) (+ alpha z))))
                           H))
         (sorted (sort matching (lambda (pair1 pair2) (< (car pair1)
                                                         (car pair2)))))
         (values (map cadr sorted))]
    values))

(define-metafunction Patina-machine
  lvselect : srs H V T lv -> (hv ...)
  
  [(lvselect srs H V T lv)
   ,(select (term H) (term alpha) (term z))

   (where ty (lvtype srs T lv))
   (where alpha (lvaddr srs H V T lv))
   (where z (sizeof srs ty))])

(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V c)
                                    (struct C (b1) (a b)))
                            ,test-V
                            ,test-T
                            c))
            (term ((int 23) (int 24) (ptr 98))))
