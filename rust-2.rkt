#lang racket

(require redex
         rackunit)

(define-language Patina
  (prog (srs fns))
  ;; structures:
  (srs (sr ...))
  (sr (struct s ls (ty ...)))
  ;; lifetimes:
  (ls (l ...))
  ;; function def'ns
  (fns (fn ...))
  (fn (fun g ls ((x : ty) ...) bk))
  ;; blocks:
  (bk (block l (let (x : ty) ...) sts))
  ;; statements:
  [sts (st ...)]
  (st (lv = rv)
      (call g ls lvs)
      bk)
  ;; lvalues :
  ;; changing "field names" to be numbers
  (lvs (lv ...))
  (lv x (lv : f) (* lv))
  ;; rvalues :
  (rv (cm lv)                      ;; copy lvalue
      (& l mq lv)             ;; take address of lvalue
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
  [C (prog H V T S)]
  ;; H (heap) : maps addresses to heap values
  [H ((alpha hv) ...)]
  ;; hv (heap values)
  [hv (ptr alpha) (int number) void]
  ;; V: maps variable names to addresses
  [V (vmap ...)]
  [vmap ((x alpha) ...)]
  ;; T : a map from names to types
  [T (tmap ...)]
  [tmap ((x ty) ...)]
  ;; S (stack) : stack-frames contain pending statements
  [S (sf ...)]
  [sf (l sts)]
  [(alphas betas gammas) (number ...)]
  [(alpha beta gamma) number]
  ;; z -- sizes, offsets
  [zs (z ...)]
  [z number])

;; unit test setup for helper fns

(define test-main
  (term (fun main [a] [(outp : (& a mut int))]
             (block l0 (let) [((* outp) = 22)]))))

(check-not-false (redex-match Patina-machine fn test-main))

(define test-fns (term [,test-main]))

(check-not-false (redex-match Patina-machine fns test-fns))

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

(check-not-false (redex-match Patina-machine srs test-srs))

(define test-prog
  (term (,test-srs ,test-fns)))

(check-not-false (redex-match Patina-machine prog test-prog))

(define test-T (term (((i int)
                       (p (~ int)))
                      ((a (struct-ty A ()))
                       (b (struct-ty B (static)))
                       (c (struct-ty C (static)))
                       (q (& b1 imm int))
                       (r (~ int))))))

(check-not-false (redex-match Patina-machine T test-T))

(define test-V (term (((i 10)
                       (p 11))
                      ((a 12)
                       (b 13)
                       (c 15)
                       (q 18)
                       (r 19)))))

(define test-H (term [(10 (int 22)) ;; i == 22
                      (11 (ptr 99)) ;; p == 99
                      (12 (int 23)) ;; a:0
                      (13 (int 24)) ;; b:0
                      (14 (ptr 98)) ;; b:1
                      (15 (int 25)) ;; c:1:0
                      (16 (int 26)) ;; c:1:0
                      (17 (ptr 97)) ;; c:1:1
                      (18 (ptr 98)) ;; q
                      (19 (ptr 96)) ;; r
                      (96 (int 27))   ;; *c:1:1
                      (97 (int 28))   ;; *c:1:1
                      (98 (int 29))   ;; *b:1
                      (99 (int 30))])) ;; *p

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; initial -- the initial state of the machine

(define initial-H (term [(0 (int 0))       ;; static value for result code
                         (1 (ptr 0))]))    ;; pointer to result code
(check-not-false (redex-match Patina-machine H initial-H))

(define initial-V (term [[(resultp 1)]]))
(check-not-false (redex-match Patina-machine V initial-V))

(define initial-T (term [[(resultp (& l0 mut int))]]))
(check-not-false (redex-match Patina-machine T initial-T))

(define initial-S (term [(l0 [(call main (l0) (resultp))])]))
(check-not-false (redex-match Patina-machine S initial-S))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sort-heap -- sort heap address in ascending order

(define (sort-heap heap)
  (sort heap (lambda (pair1 pair2) (< (car pair1)
                                      (car pair2)))))

;; useful heap predicates

(define (in-range addr base size)
  (and (>= addr base)
       (< addr (+ base size))))

(define (select H alpha z)
  (let* [(matching (filter (lambda (pair) (in-range (car pair) alpha z)) H))
         (sorted (sort-heap matching))
         (values (map cadr sorted))]
    values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; deref function -- search a heap for a given address.

(define-metafunction Patina-machine
  deref : H alpha -> hv

  [(deref H alpha)
   ,(get (term alpha) (term H))])

(test-equal (term (deref [(1 (ptr 22))] 1)) (term (ptr 22)))
(test-equal (term (deref [(2 (ptr 23)) (1 (int 22))] 1)) (term (int 22)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; fun-defn -- 

(define-metafunction Patina-machine
  fun-defn : fns g -> fn
  
  [(fun-defn (fn_0 fn_1 ...) g)
   fn_0
   (where (fun g ls ((x : ty) ...) bk) fn_0)]

  [(fun-defn (fn_0 fn_1 ...) g)
   (fun-defn (fn_1 ...) g)])

(test-equal (term (fun-defn ,test-fns main))
            (term ,test-main))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; extend -- grows a heap with z contiguous new addresses 

(define-metafunction Patina-machine
  extend : H alpha z -> H
  
  [(extend H alpha 0) H]

  [(extend ((beta hv) ...) alpha z)
   (extend ((alpha void) (beta hv) ...)
            ,(add1 (term alpha))
            ,(sub1 (term z)))])

(test-equal (term (extend [(10 (ptr 1))
                           (11 (int 2))
                           (12 (ptr 3))]
                           13
                           3))
            (term [(15 void)
                   (14 void)
                   (13 void)
                   (10 (ptr 1))
                   (11 (int 2))
                   (12 (ptr 3))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; shrink -- removes z contiguous addresses from domain of heap

(define-metafunction Patina-machine
  shrink : H alpha z -> H
  
  [(shrink H alpha z)
   ,(filter (lambda (pair) (not (in-range (car pair) (term alpha) (term z))))
            (term H))])

(test-equal (term (shrink [(10 (ptr 1))
                           (11 (int 2))
                           (12 (ptr 3))
                           (13 (ptr 4))
                           (14 (ptr 5))]
                           11
                           3))
            (term [(10 (ptr 1))
                   (14 (ptr 5))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; is-void -- test for void

(define-metafunction Patina-machine
  is-void : hv -> boolean

  [(is-void void) #t]
  [(is-void (ptr alpha)) #f]
  [(is-void (int number)) #f])

(test-equal (term (is-void (ptr 2))) #f)
(test-equal (term (is-void void)) #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; deinit -- deinitializes a block of memory

(define-metafunction Patina-machine
  deinit : H alpha z -> H
  
  [(deinit H alpha 0) H]

  [(deinit H alpha z)
   (deinit (update H alpha void)
            ,(add1 (term alpha))
            ,(sub1 (term z)))])

(define-metafunction Patina-machine
  lvdeinit : srs H V T lv -> H

  [(lvdeinit srs H V T lv)
   (deinit H alpha z)
   (where ty (lvtype srs T lv))
   (where alpha (lvaddr srs H V T lv))
   (where z (sizeof srs ty))])

(test-equal (term (deinit [(10 (ptr 1))
                           (11 (int 2))
                           (12 (ptr 3))
                           (13 (ptr 4))
                           (14 (ptr 5))]
                           11
                           3))
            (term [(10 (ptr 1))
                   (11 void)
                   (12 void)
                   (13 void)
                   (14 (ptr 5))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; memcopy -- copies memory from one address to another

(define-metafunction Patina-machine
  memcopy : H alpha beta z -> H
  
  [(memcopy H alpha beta 0) H]

  [(memcopy H alpha beta z)
   (memcopy (update H alpha (deref H beta))
            ,(add1 (term alpha))
            ,(add1 (term beta))
            ,(sub1 (term z)))])

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; memmove -- copies memory then deinitializes the source

(define-metafunction Patina-machine
  memmove : H alpha beta z -> H
  
  [(memmove H alpha beta z)
   (deinit (memcopy H alpha beta z) beta z)])

(test-equal (term (memmove [(10 (ptr 1))
                            (11 (int 2))
                            (12 (ptr 3))
                            (20 (ptr 4))
                            (21 (int 5))
                            (22 (ptr 6))]
                           20
                           10
                           3))
            (term [(10 void)
                   (11 void)
                   (12 void)
                   (20 (ptr 1))
                   (21 (int 2))
                   (22 (ptr 3))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; vtype -- lookup type of variable in V
 
(define-metafunction Patina-machine
  vtype : T x -> ty
  
  [(vtype T x_0)
   ,(get* (term x_0) (term T))])

(test-equal (term (vtype ,test-T i)) (term int))

(test-equal (term (vtype ,test-T c)) (term (struct-ty C (static))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; struct-tys

(define-metafunction Patina-machine
  struct-tys : srs s ls -> (ty ...)
  
  [(struct-tys ((struct s_0 (l_0 ...) (ty_0 ...)) sr ...) s_0 ls_1)
   (ty_0 ...)] ;; FIXME subst lifetimes

  [(struct-tys ((struct s_0 (l_0 ...) (ty_0 ...)) sr ...) s_1 ls_1)
   (struct-tys (sr ...) s_1 ls_1)])

(test-equal (term (struct-tys ,test-srs A ()))
            (term (int)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sizeof

(define-metafunction Patina-machine
  sizeof : srs ty -> z
  
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; malloc -- extend heap z contiguous addresses and retun starting address

(define-metafunction Patina-machine
  malloc : H z -> (H alpha)

  [(malloc H z)
   (H_1 beta)
   (where (alpha ...) ,(map car (term H)))
   (where beta ,(add1 (apply max (term (-1 alpha ...)))))
   (where H_1 (extend H beta z))])

(test-equal (cadr (term (malloc ,test-H 2))) 100)
(test-equal (cadr (term (malloc () 2))) 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; movemany -- like memmove but for a series of regions

(define-metafunction Patina-machine
  movemany : H zs alphas betas -> H

  [(movemany H () () ())
   H]

  [(movemany H (z_0 z_1 ...) (alpha_0 alpha_1 ...) (beta_0 beta_1 ...))
   (movemany (memmove H alpha_0 beta_0 z_0)
             (z_1 ...)
             (alpha_1 ...)
             (beta_1 ...))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rveval -- evaluate an rvalue and store it into the heap at address alpha

(define-metafunction Patina-machine
  rveval : srs H V T alpha rv -> H

  [(rveval srs H V T alpha (copy lv))
   H_1
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where beta (lvaddr srs H V T lv))
   (where H_1 (memcopy H alpha beta z))]

  [(rveval srs H V T alpha (move lv))
   H_1
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where beta (lvaddr srs H V T lv))
   (where H_1 (memmove H alpha beta z))]

  [(rveval srs H V T alpha (& l mq lv))
   H_1
   (where beta (lvaddr srs H V T lv))
   (where H_1 (update H alpha (ptr beta)))]

  [(rveval srs H V T alpha (struct s ls lvs))
   (movemany H zs_0 betas alphas)

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
   (update H_2 alpha (ptr gamma))

   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where beta (lvaddr srs H V T lv))
   (where (H_1 gamma) (malloc H z))
   (where H_2 (memmove H_1 gamma beta z))]
   
  [(rveval srs H V T alpha number)
   (update H alpha (int number))]
   
  [(rveval srs H V T alpha (+ lv_0 lv_1))
   (update H alpha (int number_2))

   (where beta (lvaddr srs H V T lv))
   (where gamma (lvaddr srs H V T lv))
   (where (int number_0) (deref H beta))
   (where (int number_1) (deref H gamma))
   (where number_2 ,(+ (term number_0) (term number_1)))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lvselect -- helper for writing tests, selects values for a portion
;; of the heap

(define-metafunction Patina-machine
  lvselect : srs H V T lv -> (hv ...)
  
  [(lvselect srs H V T lv)
   ,(select (term H) (term alpha) (term z))

   (where ty (lvtype srs T lv))
   (where alpha (lvaddr srs H V T lv))
   (where z (sizeof srs ty))])

;; tests for rveval and lvselect

(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V c)
                                    (struct C (b1) (a b)))
                            ,test-V
                            ,test-T
                            c))
            (term ((int 23) (int 24) (ptr 98))))

(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V c)
                                    (struct C (b1) (a b)))
                            ,test-V
                            ,test-T
                            a))
            (term (void)))

(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V p)
                                    (new i))
                            ,test-V
                            ,test-T
                            p))
            (term ((ptr 100))))

(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V p)
                                    (new i))
                            ,test-V
                            ,test-T
                            p))
            (term ((ptr 100))))

(test-equal (term (deref (rveval ,test-srs ,test-H ,test-V ,test-T
                                 (vaddr ,test-V p)
                                 (new i)) 100))
            (term (int 22))) ;; *p now contains value of i

(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V q)
                                    (& mq imm (* ((c : 1) : 1))))
                            ,test-V
                            ,test-T
                            q))
            (term ((ptr 97))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; free -- frees the memory owned by `alpha` which has type `ty`
;;
;; Note that this does *not* free (or deinitialize) `alpha` itself!

(define-metafunction Patina-machine
  free-struct : srs H alpha (ty ...) (z ...) -> H

  [(free-struct srs H alpha () ())
   H]

  [(free-struct srs H alpha (ty_0 ty_1 ...) (z_0 z_1 ...))
   (free-struct srs (free srs H ty_0 beta) alpha (ty_1 ...) (z_1 ...))
   (where beta ,(+ (term alpha) (term z_0)))])

(define-metafunction Patina-machine
  free : srs H ty alpha -> H

  [(free srs H ty alpha)
   H
   (side-condition (term (is-void (deref H alpha))))]
  
  [(free srs H int alpha) H]

  [(free srs H (& l mq ty) alpha) H]

  [(free srs H (~ ty) alpha)
   H_2
   (where (ptr beta) (deref H alpha))
   (where z (sizeof srs ty))
   (where H_1 (free srs H ty beta))
   (where H_2 (shrink H beta z))]
  [(free srs H (struct-ty s ls) alpha)
   (free-struct srs H alpha tys zs)
   (where tys (struct-tys srs s ls))
   (where zs (offsets srs s ls))])

(define-metafunction Patina-machine
  lvfree : srs H V T lv -> H

  [(lvfree srs H V T lv)
   (free srs H ty alpha)
   (where ty (lvtype srs T lv))
   (where alpha (lvaddr srs H V T lv))])

(test-equal (term (lvfree ,test-srs ,test-H ,test-V ,test-T p))
            (term (shrink ,test-H 99 1)))

(test-equal (term (lvdeinit ,test-srs
                            (lvfree ,test-srs ,test-H ,test-V ,test-T p)
                            ,test-V
                            ,test-T
                            p))
            (term (deinit (shrink ,test-H 99 1) 11 1)))
            
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; free-variables -- free variables upon exit from a block,
;; also removes memory used by those variables

(define-metafunction Patina-machine
  free-variables : srs H vmap tmap -> H

  [(free-variables srs H () ()) H]
  [(free-variables srs
                   H
                   ((x_0 alpha_0) (x_1 alpha_1) ...)
                   ((x_0 ty_0) (x_1 ty_1) ...))
   (shrink (free srs H_1 ty_0 alpha_0) alpha_0 z)
   (where z (sizeof srs ty_0))
   (where H_1 (free-variables srs
                              H
                              ((x_1 alpha_1) ...)
                              ((x_1 ty_1) ...)))])

;; this should free up all memory but that which pertains to `i` and `p`,
;; as well as `97` and `98` which are marked as 'static'
(test-equal (term (free-variables ,test-srs
                                  ,test-H
                                  ,(cadr test-V)
                                  ,(cadr test-T)))
            (term ((10 (int 22))
                   (11 (ptr 99))
                   (97 (int 28))
                   (98 (int 29))
                   (99 (int 30)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; alloc-variables -- allocate space for variables upon entry to a block,
;; filling the memory with void

(define-metafunction Patina-machine
  alloc-variables : srs H ((x : ty) ...) -> (vmap tmap H)

  [(alloc-variables srs H ()) (() () H)]
  [(alloc-variables srs H ((x_0 : ty_0) (x_1 : ty_1) ...))
   (((x_0 alpha_0) (x_2 alpha_2) ...)
    ((x_0 ty_0) (x_2 ty_2) ...)
    H_2)
   (where z (sizeof srs ty_0))
   (where (H_1 alpha_0) (malloc H z))
   (where (((x_2 alpha_2) ...)
           ((x_2 ty_2) ...)
           H_2) (alloc-variables srs H_1 ((x_1 : ty_1) ...)))])

;; this should free up all memory but that which pertains to `i` and `p`,
;; as well as `97` and `98` which are marked as 'static'
(test-equal (term (alloc-variables ,test-srs
                                   ,test-H
                                   ((j : int)
                                    (k : (struct-ty B (static))))))
            (term (((j 100) (k 101))
                   ((j int) (k (struct-ty B (static))))
                   ,(append (term ((102 void) (101 void) (100 void)))
                            test-H))))

;; --> -- machine step from one configuration C to the next

(define machine-step
  (reduction-relation
   Patina-machine
   
   ;; Stack frame with no more statements. Free variables.
   [--> ((srs fns) H [vmap_0 vmap_1 ...] [tmap_0 tmap_1 ...]
         [(l ()) sf_1 ...])
        ((srs fns) H_1 [vmap_1 ...] [tmap_1 ...] [sf_1 ...])
        (where H_1 (free-variables srs H vmap_0 tmap_0))]

   ;; Assignments. The memory for the lvalue should always be alloc'd,
   ;; though not always init'd.
   [--> ((srs fns) H V T [(l ((lv = rv) st ...)) sf ...])
        ((srs fns) H_1 V T [(l (st ...)) sf ...])
        (where alpha (lvaddr srs H V T lv))
        (where H_1 (rveval srs H V T alpha rv))]

   ;; Push a new block.
   [--> ((srs fns) H (vmap ...) (tmap ...)
         [sf_1 sf_2 ...])
        ((srs fns) H_1  [vmap_b vmap ...] [tmap_b tmap ...]
         [sf_b (l_1 [st_1 ...]) sf_2 ...])

        ;; unpack the top-most stack frame sf_1:
        (where (l_1 [st_0 st_1 ...]) sf_1)
        ;; unpack the next statement st_0, which should be a block:
        (where (block l_b (let (x_b : ty_b) ...) (st_b ...)) st_0)
        ;; allocate space for block svariables in memory:
        (where (vmap_b tmap_b H_1) (alloc-variables srs H ((x_b : ty_b) ...)))
        ;; create new stack frame for block
        ;; FIXME substitute a fresh lifetime for l_b
        (where sf_b (l_b (st_b ...)))
        ]

   ;; Push a call.
   [--> ((srs fns) H V T S)
        ((srs fns) H_2 [vmap_a vmap ...] [tmap_a tmap ...]
         [(lX (bk_f)) (l_1 [st_r ...]) sf_r ...])

        ;; unpack V and T for later expansion
        (where ([vmap ...] [tmap ...]) (V T))
        ;; unpack the stack frames:
        (where [(l_1 sts_1) sf_r ...] S)
        ;; unpack the statements sts_1 from top-most activation:
        (where ((call g ls_a lvs_a) st_r ...) sts_1)
        ;; determine the types of the actual args to be passed:
        (where tys_a ,(map (lambda (lv) (term (lvtype srs T ,lv)))
                           (term lvs_a)))
        ;; determine sizes of those types
        (where zs_a ,(map (lambda (ty) (term (sizeof srs ,ty)))
                          (term tys_a)))
        ;; determine where lvalues are found in memory
        (where alphas_a ,(map (lambda (lv) (term (lvaddr srs H V T ,lv)))
                              (term lvs_a)))
        ;; lookup the fun def'n (FIXME s/ls_f/ls_a/):
        (where (fun g ls_f ((x_f : ty_f) ...) bk_f) (fun-defn fns g))
        ;; allocate space for parameters in memory:
        (where (vmap_a tmap_a H_1) (alloc-variables srs H ((x_f : ty_f) ...)))
        ;; determine addresses for each formal argument:
        (where betas_f ,(map (lambda (lv) (term (lvaddr srs H_1
                                                        (vmap_a) (tmap_a)
                                                        ,lv)))
                             (term (x_f ...))))
        ;; move from actual params into formal params:
        (where H_2 (movemany H_1 zs_a betas_f alphas_a))
        ]
   ))

;; test stepping where top-most stack frame has no remaining statements
(test--> machine-step
         (term (,test-prog () (()) (()) ((l0 ()))))
         (term (,test-prog () () () ())))

;; test popping off a stack frame with vars and another frame beneath
(test--> machine-step
         (term (,test-prog
                [(0 (int 22)) (1 (int 23))]
                [[(j 1)] [(i 0)]]
                [[(j int)] [(i int)]]
                [(l0 []) (l1 [])]))
         (term (,test-prog
                [(0 (int 22))]
                [[(i 0)]]
                [[(i int)]]
                [(l1 [])])))

;;;; test pushing a new block
(test--> machine-step
         (term (,test-prog
                [(0 (int 22))]
                [[(a 0)]]
                [[(a int)]]
                [(l1 [(block l2 (let (b : int) (c : (~ int)))
                             ((i = 2) (j = (new i))))])]))
          (term (,test-prog
                 [(2 void) (1 void) (0 (int 22))]
                 [[(b 1) (c 2)] [(a 0)]]
                 [[(b int) (c (~ int))] [(a int)]]
                 [(l2 [(i = 2) (j = (new i))])
                  (l1 [])])))

;; test a series of state steps, starting from the initial state.
;; This tests:
;; - function calls
;; - block activation
;; - assignment (through a pointer)
;; - popping

(define state-0
  (term (,test-prog ,initial-H ,initial-V ,initial-T ,initial-S)))
(check-not-false (redex-match Patina-machine C state-0))

(define state-1
  (term (,test-prog
         [(2 (ptr 0)) (0 (int 0)) (1 void)]
         [[(outp 2)] [(resultp 1)]]
         [[(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(lX [(block l0 (let) (((* outp) = 22)))])
          (l0 [])])))
(check-not-false (redex-match Patina-machine C state-1))

(define state-2
  (term (,test-prog
         [(2 (ptr 0)) (0 (int 0)) (1 void)]
         [[] [(outp 2)] [(resultp 1)]]
         [[] [(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(l0 [((* outp) = 22)])
          (lX [])
          (l0 [])])))
(check-not-false (redex-match Patina-machine C state-2))

(define state-3
  (term (,test-prog
         [(2 (ptr 0)) (0 (int 22)) (1 void)]
         [[] [(outp 2)] [(resultp 1)]]
         [[] [(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(l0 [])
          (lX [])
          (l0 [])])))
(check-not-false (redex-match Patina-machine C state-3))

(define state-N
  (term (,test-prog
         [(0 (int 22))]
         []
         []
         [])))
(check-not-false (redex-match Patina-machine C state-N))

(test--> machine-step state-0 state-1)
(test--> machine-step state-1 state-2)
(test--> machine-step state-2 state-3)
(test-->> machine-step state-0 state-N)
