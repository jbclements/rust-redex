;; -*- coding: utf-8; -*-

;; Cheat sheet for unicode, using M-x set-input-method as TeX:
;; \alpha -> α
;; \beta  -> β
;; \gamma -> γ
;; \cdot  -> ·
;; \ell   -> ℓ

#lang racket

(require redex
         rackunit)

(define-language Patina
  (prog (srs fns))
  ;; structures:
  (srs (sr ...))
  (sr (struct s ℓs (ty ...)))
  ;; lifetimes:
  (ℓs (ℓ ...))
  ;; function def'ns
  (fns (fn ...))
  (fn (fun g ℓs vdecls bk))
  ;; blocks:
  (bk (block ℓ vdecls sts))
  ;; variable decls
  (vdecls [vdecl ...])
  (vdecl (x : ty))
  ;; statements:
  [sts (st ...)]
  (st (lv = rv)
      (call g ℓs lvs)
      (match lv (Some mode x => bk) (None => bk))
      bk)
  ;; lvalues :
  ;; changing "field names" to be numbers
  (lvs (lv ...))
  (lv x                            ;; variable
      (lv · f)                     ;; field projection
      (lv @ lv)                    ;; indexing
      (* lv))                      ;; deref
  ;; rvalues :
  (rv (cm lv)                      ;; copy lvalue
      (& ℓ mq lv)                  ;; take address of lvalue
      (struct s ℓs (lv ...))       ;; struct constant
      (new lv)                     ;; allocate memory
      number                       ;; constant number
      (lv + lv)                    ;; sum
      (Some lv)
      None
      (vec lv ...)
      )
  (cm copy move)
  (mode (ref mq) move)
  ;; types : 
  (tys (ty ...))
  (ty (struct s ℓs)             ;; s<'ℓ...>
      (~ ty)                       ;; ~t
      (& ℓ mq ty)                  ;; &'ℓ mq t
      int
      (Option ty)
      (vec ty z)
      (vec ty))
  ;; mq : mutability qualifier
  (mq mut imm)
  ;; variables
  (x variable-not-otherwise-mentioned)
  ;; function names
  (g variable-not-otherwise-mentioned)
  ;; structure names
  (s variable-not-otherwise-mentioned)
  ;; labels
  (ℓ variable-not-otherwise-mentioned)
  ;; field "names"
  (f number)
  ;; z -- sizes, offsets
  [zs (z ...)]
  [z number]
  ;; hack for debugging
  (debug debug-me)
  )

(check-not-false (redex-match Patina ty (term (vec int 3))))

;;;;
;;
;; EVALUATION
;;
;;;;

(define-extended-language Patina-machine Patina
  ;; a configuration of the machine
  [C (prog H V T S)]
  ;; H (heap) : maps addresses to heap values
  [H ((α hv) ...)]
  ;; hv (heap values)
  [hv (ptr α) (int number) void]
  ;; V: maps variable names to addresses
  [V (vmap ...)]
  [vmap ((x α) ...)]
  ;; T : a map from names to types
  [T (tmap ...)]
  [tmap ((x ty) ...)]
  ;; S (stack) : stack-frames contain pending statements
  [S (sf ...)]
  [sf (ℓ sts)]
  [(αs βs γs) (number ...)]
  [(α β γ) number]
  )

;; unit test setup for helper fns

(define test-srs
  (term [(struct A () (int))
         (struct B (l0) (int (& l0 mut int)))
         (struct C (l0) ((struct A ())
                         (struct B (l0))))
         (struct D (l0) ((struct C (l0))
                         (struct A ())
                         (struct C (l0))
                         (struct B (l0))))
         ]))

(check-not-false (redex-match Patina-machine srs test-srs))

(define test-T (term [[(i int)
                       (p (~ int))]
                      [(a (struct A ()))
                       (b (struct B (static)))
                       (c (struct C (static)))
                       (q (& b1 imm int))
                       (r (~ int))
                       (s (Option (~ int)))
                       (ints (vec int 3))
                       (i0 int)
                       (i1 int)
                       (i2 int)
                       (i3 int)]]))
(check-not-false (redex-match Patina-machine T test-T))

(define test-V (term (((i 10)
                       (p 11))
                      ((a 12)
                       (b 13)
                       (c 15)
                       (q 18)
                       (r 19)
                       (s 20)
                       (ints 22)
                       (i0 25)
                       (i1 26)
                       (i2 27)
                       (i3 28)))))
(check-not-false (redex-match Patina-machine V test-V))

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
                      (20 (int 1))  ;; s – discriminant
                      (21 (ptr 95)) ;; s – payload
                      (22 (int 10)) ;; ints @ 0
                      (23 (int 11)) ;; ints @ 1
                      (24 (int 12)) ;; ints @ 2
                      (25 (int 0))  ;; i0
                      (26 (int 1))  ;; i1
                      (27 (int 2))  ;; i2
                      (28 (int 3))  ;; i3
                      (95 (int 31))   ;; *payload(s)
                      (96 (int 30))   ;; *c:1:1
                      (97 (int 29))   ;; *c:1:1
                      (98 (int 28))   ;; *b:1
                      (99 (int 27))])) ;; *p
(check-not-false (redex-match Patina-machine H test-H))

(define test-dst-srs
  (term [(struct RCDataInt3 () [int [vec int 3]])
         (struct RCInt3 () [(& static imm (struct RCDataInt3 []))])
         (struct RCDataIntN () (int [vec int]))
         (struct RCIntN () [(& static imm (struct RCDataIntN []))])
         (struct Cycle1 () [(Option (~ (struct Cycle []))) (vec int)])
         (struct Cycle2 () [(Option (~ (struct Cycle [])))])
         ]))

(check-not-false (redex-match Patina-machine srs test-dst-srs))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; simple test prog that assigns to the result pointer

(define twentytwo-main
  (term (fun main [a] [(outp : (& a mut int))]
             (block l0 [] [((* outp) = 22)]))))

(check-not-false (redex-match Patina-machine fn twentytwo-main))

(define twentytwo-fns (term [,twentytwo-main]))
(check-not-false (redex-match Patina-machine fns twentytwo-fns))

(define twentytwo-prog
  (term (,test-srs ,twentytwo-fns)))
(check-not-false (redex-match Patina-machine prog twentytwo-prog))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test prog that creates a linked list and counts down

(define sum-srs
  (term [(struct List () (int
                          (Option (~ (struct List [])))))]))
(check-not-false (redex-match Patina-machine srs sum-srs))

(define sum-main
  (term (fun main [a] [(outp : (& a mut int))]
             (block l0 [(i : int)
                        (n : (Option (~ (struct List []))))
                        (s : (struct List []))
                        (l : (~ (struct List [])))
                        (p : (& l0 imm (struct List [])))]
                    [(i = 22)
                     (n = None)
                     (s = (struct List [] (i n)))
                     (l = (new s))
                     (i = 44)
                     (n = (Some l))
                     (s = (struct List [] (i n)))
                     (l = (new s))
                     (p = (& l0 imm (* l)))
                     (call sum_list [l0 a] [p outp])]))))
(check-not-false (redex-match Patina-machine fn sum-main))

;; fn sum_list(inp: &List, outp: &mut int) {
;;     let r: int = inp.0;
;;     match inp.1 {
;;         Some(ref next1) => { // next1: &~List
;;             let next2 = &**next1;
;;             let b = 0;
;;             {
;;                 let c = &mut b;
;;                 sum_list(next2, c);
;;             }
;;             *outp = r + b;
;;         }
;;         None => {
;;             *outp = r + b;
;;         }
;;     }
;; }
(define sum-sum_list
  (term (fun sum_list [a b] [(inp : (& a imm (struct List [])))
                             (outp : (& b mut int))]
             (block l0
                    [(r : int)]
                    [(r = (copy ((* inp) · 0)))
                     (match ((* inp) · 1)
                       (Some (ref imm) next1 =>
                             (block l1 [(next2 : (& l1 imm (struct List [])))
                                        (b : int)]
                                    [(next2 = (& l1 imm (* (* next1))))
                                     (b = 0)
                                     (block l2 [(c : (& l1 mut int))]
                                            [(c = (& l2 mut b))
                                             (call sum_list [l1 l2] [next2 c])
                                             ((* outp) = (r + b))])]))
                       (None =>
                             (block l2 []
                                    [((* outp) = (copy r))])))]))))
(check-not-false (redex-match Patina-machine fn sum-sum_list))

(define sum-fns
  (term (,sum-main ,sum-sum_list)))

(define sum-prog
  (term (,sum-srs ,sum-fns)))
(check-not-false (redex-match Patina-machine prog sum-prog))

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
  (sort heap (λ (pair1 pair2) (< (car pair1)
                                      (car pair2)))))

;; useful heap predicates

(define (in-range addr base size)
  (and (>= addr base)
       (< addr (+ base size))))

(define (select H α z)
  (let* [(matching (filter (λ (pair) (in-range (car pair) α z)) H))
         (sorted (sort-heap matching))
         (values (map cadr sorted))]
    values))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; reject – useful for debugging since it causes contract errors

(define-metafunction Patina-machine
  reject : debug -> number

  [(reject debug) 0])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sum

(define-metafunction Patina-machine
  sum : zs -> z
  
  [(sum []) 0]
  [(sum [z_0 z_1 ...])
   ,(+ (term z_0) (term (sum [z_1 ...])))]

  )

(test-equal (term (sum [1 2 3]))
            (term 6))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; prefix sum

(define-metafunction Patina-machine
  prefix-sum : z zs -> zs
  
  [(prefix-sum z_a ()) ()]
  [(prefix-sum z_a (z_b z_c ...))
   [z_d z_e ...]
   (where z_d (sum [z_a z_b]))
   (where [z_e ...] (prefix-sum z_d [z_c ...]))]

  )

(test-equal (term (prefix-sum 0 ()))
            (term ()))

(test-equal (term (prefix-sum 0 (1 2 3)))
            (term (1 3 6)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; offset, inc, and dec

(define-metafunction Patina-machine
  offset : α z -> α

  [(offset α z) ,(+ (term α) (term z))])

(define-metafunction Patina-machine
  inc : α -> α

  [(inc z) ,(add1 (term z))])

(define-metafunction Patina-machine
  dec : α -> α

  [(dec z) ,(sub1 (term z))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; deref function -- search a heap for a given address.

(define-metafunction Patina-machine
  deref : H α -> hv

  [(deref H α)
   ,(get (term α) (term H))])

(test-equal (term (deref [(1 (ptr 22))] 1)) (term (ptr 22)))
(test-equal (term (deref [(2 (ptr 23)) (1 (int 22))] 1)) (term (int 22)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; fun-defn -- 

(define-metafunction Patina-machine
  fun-defn : fns g -> fn
  
  [(fun-defn (fn_0 fn_1 ...) g)
   fn_0
   (where (fun g ℓs ((x : ty) ...) bk) fn_0)]

  [(fun-defn (fn_0 fn_1 ...) g)
   (fun-defn (fn_1 ...) g)])

(test-equal (term (fun-defn ,twentytwo-fns main))
            (term ,twentytwo-main))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; update -- replaces value for α

(define-metafunction Patina-machine
  update : H α hv -> H
  
  [(update ((α_0 hv_0) (α_1 hv_1) ...) α_0 hv_2)
   ((α_0 hv_2) (α_1 hv_1) ...)]

  [(update ((α_0 hv_0) (α_1 hv_1) ...) α_2 hv_2)
   ,(append (term ((α_0 hv_0))) (term (update ((α_1 hv_1) ...) α_2 hv_2)))])

(test-equal (term (update [(2 (ptr 23)) (1 (int 22))] 1 (int 23)))
            (term ((2 (ptr 23)) (1 (int 23)))))

(test-equal (term (update [(2 (ptr 23)) (1 (int 22))] 2 (int 23)))
            (term ((2 (int 23)) (1 (int 22)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; extend -- grows a heap with z contiguous new addresses 

(define-metafunction Patina-machine
  extend : H α z -> H
  
  [(extend H α 0) H]

  [(extend ((β hv) ...) α z)
   (extend ((α void) (β hv) ...)
            ,(add1 (term α))
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
  shrink : H α z -> H
  
  [(shrink H α z)
   ,(filter (λ (pair) (not (in-range (car pair) (term α) (term z))))
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
  [(is-void (ptr α)) #f]
  [(is-void (int number)) #f])

(test-equal (term (is-void (ptr 2))) #f)
(test-equal (term (is-void void)) #t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; field-tys

(define-metafunction Patina-machine
  field-tys : srs s ℓs -> (ty ...)
  
  [(field-tys ((struct s_0 (ℓ_0 ...) (ty_0 ...)) sr ...) s_0 ℓs_1)
   (ty_0 ...)] ;; FIXME subst lifetimes

  [(field-tys ((struct s_0 (ℓ_0 ...) (ty_0 ...)) sr ...) s_1 ℓs_1)
   (field-tys (sr ...) s_1 ℓs_1)])

(test-equal (term (field-tys ,test-srs A ()))
            (term (int)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; is-DST

(define-metafunction Patina-machine
  is-DST : srs ty -> boolean

  [(is-DST srs ty) (is-DST-1 [] srs ty)])

(define-metafunction Patina-machine
  is-DST-1 : [s ...] srs ty -> boolean

  [(is-DST-1 [s_a ...] srs (struct s ℓs))
   #false
   (side-condition (member (term s) (term [s_a ...])))]
  [(is-DST-1 [s_a ...] srs (struct s ℓs))
   (is-DST-1 [s s_a ...] srs ty_z)
   (where (ty_a ... ty_z) (field-tys srs s ℓs))]
  [(is-DST-1 [s ...] srs (~ ty)) #false]
  [(is-DST-1 [s ...] srs (& ℓ mq ty)) #false]
  [(is-DST-1 [s ...] srs int) #false]
  [(is-DST-1 [s ...] srs (Option ty)) (is-DST-1 [s ...] srs ty)]
  [(is-DST-1 [s ...] srs (vec ty)) #true]
  [(is-DST-1 [s ...] srs (vec ty z)) #false])

(test-equal (term (is-DST ,test-dst-srs (~ (vec int))))
            #false)

(test-equal (term (is-DST ,test-dst-srs (vec int)))
            #true)

(test-equal (term (is-DST ,test-dst-srs (struct RCDataInt3 [])))
            #false)

(test-equal (term (is-DST ,test-dst-srs (struct RCInt3 [])))
            #false)

(test-equal (term (is-DST ,test-dst-srs (struct RCDataIntN [])))
            #true)

(test-equal (term (is-DST ,test-dst-srs (struct RCIntN [])))
            #false)

(test-equal (term (is-DST ,test-dst-srs (struct Cycle1 [])))
            #true)

(test-equal (term (is-DST ,test-dst-srs (struct Cycle2 [])))
            #false)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sizeof

(define-metafunction Patina-machine
  sizeof : srs ty -> z
  
  [(sizeof srs int) 
   1]
  
  [(sizeof srs (~ ty))
   1]
  
  [(sizeof srs (& ℓ mq ty))
   1]
  
  [(sizeof srs (struct s ℓs))
   (sum [(sizeof srs ty) ...])
   (where [ty ...] (field-tys srs s ℓs))]

  [(sizeof srs (vec ty z))
   ,(* (term (sizeof srs ty)) (term z))]

  [(sizeof srs (Option ty))
   ,(add1 (term (sizeof srs ty)))]

  )

(test-equal (term (sizeof ,test-srs (struct A ())))
            (term 1))

(test-equal (term (sizeof ,test-srs (struct B (static))))
            (term 2))

(test-equal (term (sizeof ,test-srs (struct C (static))))
            (term 3))

(test-equal (term (sizeof ,test-srs (Option (struct C (static)))))
            (term 4))

(test-equal (term (sizeof ,test-srs (vec int 3)))
            (term 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; sizeof-dst

(define-metafunction Patina-machine
  sizeof-dst : srs ty hv -> z
  
  [(sizeof-dst srs (vec ty) (int z))
   ,(* (term (sizeof srs ty)) (term z))]

  [(sizeof-dst srs (struct s ℓs) hv)
   (sum [z_a z_z])
   (where [ty_a ... ty_z] (field-tys srs s ℓs))
   (where z_a (sum [(sizeof srs ty_a) ...]))
   (where z_z (sizeof-dst srs ty_z hv))]

  )

(test-equal (term (sizeof ,test-srs (struct A ())))
            (term 1))

(test-equal (term (sizeof ,test-srs (struct B (static))))
            (term 2))

(test-equal (term (sizeof ,test-srs (struct C (static))))
            (term 3))

(test-equal (term (sizeof ,test-srs (Option (struct C (static)))))
            (term 4))

(test-equal (term (sizeof ,test-srs (vec int 3)))
            (term 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; deinit -- deinitializes a block of memory

(define-metafunction Patina-machine
  deinit : H α z -> H
  
  [(deinit H α 0) H]

  [(deinit H α z)
   (deinit (update H α void)
            ,(add1 (term α))
            ,(sub1 (term z)))])

(define-metafunction Patina-machine
  lvdeinit : srs H V T lv -> H

  [(lvdeinit srs H V T lv)
   (deinit H α z)
   (where ty (lvtype srs T lv))
   (where α (lvaddr srs H V T lv))
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
  memcopy : H α β z -> H
  
  [(memcopy H α β 0) H]

  [(memcopy H α β z)
   (memcopy (update H α (deref H β))
            ,(add1 (term α))
            ,(add1 (term β))
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
  memmove : H α β z -> H
  
  [(memmove H α β z)
   (deinit (memcopy H α β z) β z)])

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
  vaddr : V x -> α
  
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

(test-equal (term (vtype ,test-T c)) (term (struct C (static))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; field-offsets -- determines the offsets of each field of a struct

(define-metafunction Patina-machine
  field-offsets : srs s ℓs -> zs
  
  [(field-offsets srs s ℓs)
   (0 z ...)
   (where (ty_a ... ty_z) (field-tys srs s ℓs))
   (where (z ...) [(sizeof srs ty_a) ...])]

  )

(test-equal (term (field-offsets ,test-srs C (static)))
            (term (0 1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; vec-offsets -- determines the offsets of each element of a vector

(define-metafunction Patina-machine
  vec-offsets : srs ty z -> zs

  [(vec-offsets srs ty 0)
   []]
  
  [(vec-offsets srs ty 1)
   [0]]
  
  [(vec-offsets srs ty z) ;; really, really inefficient. 
   (z_a ... z_y (offset z_y (sizeof srs ty)))
   (where [z_a ... z_y] (vec-offsets srs ty (dec z)))]

  )

(test-equal (term (vec-offsets ,test-srs int 3))
            (term (0 1 2)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; vec-tys -- returns the types of each element in a vector,
;; which is just the vector element type repeated N times

(define-metafunction Patina-machine
  vec-tys : srs ty z -> tys

  [(vec-tys srs ty 0)
   []]
  
  [(vec-tys srs ty 1)
   [ty]]
  
  [(vec-tys srs ty z)
   (ty ty_a ...)
   (where [ty_a ...] (vec-tys srs ty (dec z)))]

  )

(test-equal (term (vec-tys ,test-srs int 3))
            (term (int int int)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; offsetof

(define-metafunction Patina-machine
  offsetof : srs s ℓs f -> z
  
  [(offsetof srs s ℓs f)
   ,(foldl + 0 (map (λ (t) (term (sizeof srs ,t)))
                    (take (term (field-tys srs s ℓs))
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
  [(dereftype (& ℓ mq ty)) ty])

(define-metafunction Patina-machine
  fieldtype : srs ty f -> ty
  
  [(fieldtype srs (struct s ℓs) f)
   ,(car (drop (term (field-tys srs s ℓs)) (term f)))]) ; fixme--surely a better way

(define-metafunction Patina-machine
  lvtype : srs T lv -> ty
  
  [(lvtype srs T x)
   (vtype T x)]
  
  [(lvtype srs T (* lv))
   (dereftype (lvtype srs T lv))]
  
  [(lvtype srs T (lv · f))
   (fieldtype srs (lvtype srs T lv) f)])

(test-equal (term (lvtype ,test-srs ,test-T (* p))) (term int))

;; FIXME --> l0 should be static
(test-equal (term (lvtype ,test-srs ,test-T (c · 1))) (term (struct B (l0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lvaddr -- lookup addr of variable in V

(define-metafunction Patina-machine
  lvaddr : srs H V T lv -> α
  
  [(lvaddr srs H V T x)
   (vaddr V x)]
  
  [(lvaddr srs H V T (* lv))
   α
   (where (ptr α) (deref H (lvaddr srs H V T lv)))]
       
  [(lvaddr srs H V T (lv · f))
   (offset (lvaddr srs H V T lv)
           (offsetof srs s ℓs f))
   (where (struct s ℓs) (lvtype srs T lv))]

  ;; indexing into a fixed-length vector
  [(lvaddr srs H V T (lv_v @ lv_i))
   (offset α_v z_e)
   (where (vec ty_e z_v) (lvtype srs T lv_v))
   (where α_v (lvaddr srs H V T lv_v))
   (where α_i (lvaddr srs H V T lv_i))
   (where (int z_i) (deref H α_i))
   (where z_e ,(* (term z_i) (term (sizeof srs ty_e))))
   (side-condition (>= (term z_i) 0))
   (side-condition (< (term z_i) (term z_v)))
   ]

  )

(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (c · 1)))
            (term 16))

(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T ((c · 1) · 1)))
            (term 17))

(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (* ((c · 1) · 1))))
            (term 97))

(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (ints @ i1)))
            (term 23))

;(test-equal (term (lvaddr ,test-srs ,test-H ,test-V ,test-T (ints @ i4)))
;            (term 23))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; malloc -- extend heap z contiguous addresses and retun starting address

(define-metafunction Patina-machine
  malloc : H z -> (H α)

  [(malloc H z)
   (H_1 β)
   (where ((α hv) ...) H)
   (where β ,(add1 (apply max (term (-1 α ...)))))
   (where H_1 (extend H β z))])

(test-equal (cadr (term (malloc ,test-H 2))) 100)
(test-equal (cadr (term (malloc () 2))) 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; movemany -- like memmove but for a series of regions

(define-metafunction Patina-machine
  movemany : H zs αs βs -> H

  [(movemany H () () ())
   H]

  [(movemany H (z_0 z_1 ...) (α_0 α_1 ...) (β_0 β_1 ...))
   (movemany (memmove H α_0 β_0 z_0)
             (z_1 ...)
             (α_1 ...)
             (β_1 ...))])

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; rveval -- evaluate an rvalue and store it into the heap at address α

(define-metafunction Patina-machine
  rveval : srs H V T α rv -> H

  [(rveval srs H V T α (copy lv))
   H_1
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where β (lvaddr srs H V T lv))
   (where H_1 (memcopy H α β z))]

  [(rveval srs H V T α (move lv))
   H_1
   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where β (lvaddr srs H V T lv))
   (where H_1 (memmove H α β z))]

  [(rveval srs H V T α (& ℓ mq lv))
   H_1
   (where β (lvaddr srs H V T lv))
   (where H_1 (update H α (ptr β)))]

  [(rveval srs H V T α (struct s ℓs lvs))
   (movemany H zs_0 βs αs)

   ;; types of each field:
   (where tys (field-tys srs s ℓs))
   ;; sizes of each field's type:
   (where zs_0 ,(map (λ (t) (term (sizeof srs ,t))) (term tys)))
   ;; offset of each field:
   (where zs_1 (field-offsets srs s lvs))
   ;; source address of value for each field:
   (where αs ,(map (λ (lv) (term (lvaddr srs H V T ,lv))) (term lvs)))
   ;; target address for each field relative to base address α;
   (where βs ,(map (λ (z) (+ (term α) z)) (term zs_1)))]

  [(rveval srs H V T α (new lv))
   (update H_2 α (ptr γ))

   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where β (lvaddr srs H V T lv))
   (where (H_1 γ) (malloc H z))
   (where H_2 (memmove H_1 γ β z))]
   
  [(rveval srs H V T α number)
   (update H α (int number))]
   
  [(rveval srs H V T α (lv_l + lv_r))
   (update H α (int number_s))

   (where α_l (lvaddr srs H V T lv_l))
   (where α_r (lvaddr srs H V T lv_r))
   (where (int number_l) (deref H α_l))
   (where (int number_r) (deref H α_r))
   (where number_s (offset number_l number_r))]

  [(rveval srs H V T α (Some lv))
   H_2

   (where ty (lvtype srs T lv))
   (where z (sizeof srs ty))
   (where β (lvaddr srs H V T lv))
   (where α_p ,(add1 (term α)))
   (where H_1 (memmove H α_p β z))
   (where H_2 (update H_1 α (int 1)))]

  [(rveval srs H V T α None)
   (update H α (int 0))]

  [(rveval srs H V T α (vec))
   H]

  [(rveval srs H V T α (vec lv ...))
   H_1

   (where [α_e ...] ((lvaddr srs H V T lv_e) ...))
   (where (lv_a lv_b ...) lv_e)
   (where ty (lvtype srs T lv_a))
   (where z_v (len [lv_a lv_b ...]))
   (where [z_e ...] (vec-offsets srs ty z_v))
   (where [β_e ...] ((offset α z_e) ...))
   (where H_1 (movemany srs [z_e ...] [β_e ...] [α_e ...]))]

  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; lvselect -- helper for writing tests, selects values for a portion
;; of the heap

(define-metafunction Patina-machine
  lvselect : srs H V T lv -> (hv ...)
  
  [(lvselect srs H V T lv)
   ,(select (term H) (term α) (term z))

   (where ty (lvtype srs T lv))
   (where α (lvaddr srs H V T lv))
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
                                    (& mq imm (* ((c · 1) · 1))))
                            ,test-V
                            ,test-T
                            q))
            (term ((ptr 97))))

(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V i)
                                    (i + (* p)))
                            ,test-V
                            ,test-T
                            i))
            (term ((int 49))))

;; test that `None` writes a 0 into the discriminant, leaves rest unchanged
(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V s)
                                    None)
                            ,test-V
                            ,test-T
                            s))
            (term ((int 0) (ptr 95))))

;; test that `(Some p)` writes a 1 into the discriminant
(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V s)
                                    (Some p))
                            ,test-V
                            ,test-T
                            s))
            (term ((int 1) (ptr 99))))

;; test that `(Some p)` deinitializes `p`
(test-equal (term (lvselect ,test-srs
                            (rveval ,test-srs ,test-H ,test-V ,test-T
                                    (vaddr ,test-V s)
                                    (Some p))
                            ,test-V
                            ,test-T
                            p))
            (term (void)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; free -- frees the memory owned by `α` which has type `ty`
;;
;; Note that this does *not* free (or deinitialize) `α` itself!

(define-metafunction Patina-machine
  free-at-offsets : srs H α (ty ...) (z ...) -> H

  [(free-at-offsets srs H α () ())
   H]

  [(free-at-offsets srs H α (ty_0 ty_1 ...) (z_0 z_1 ...))
   (free-at-offsets srs H_1 α (ty_1 ...) (z_1 ...))
   (where H_1 (free srs H ty_0 (offset α z_0)))]
  
  )

(define-metafunction Patina-machine
  free-vec : srs H α ty z -> H

  [(free-vec srs H α ty z)
   (free-at-offsets srs H α
                    (vec-tys srs ty z)
                    (vec-offsets srs ty z))]

  )

(define-metafunction Patina-machine
  free-dst : srs H ty α hv -> H

  [(free-dst srs H (vec ty) α (int z))
   (free-vec srs H α ty z)]

  [(free-dst srs H (struct s ℓs) α)
   (free-dst srs H_1 ty_z (offset α z_z) hv)
   (where (ty_a ... ty_z) (field-tys srs s ℓs))
   (where (z_a ... z_z) (field-offsets srs s ℓs))
   (where H_1 (free-at-offsets srs H α (ty_a ...) (z_a ...)))]

  )

(define-metafunction Patina-machine
  free : srs H ty α -> H

  [(free srs H ty α)
   H
   (side-condition (term (is-void (deref H α))))]
  
  [(free srs H int α)
   H]

  [(free srs H (vec ty z) α)
   (free-vec srs H α ty z)]

  [(free srs H (& ℓ mq ty) α) H]

  [(free srs H (~ ty) α)
   H_2
   (where (ptr β) (deref H α))
   (where z (sizeof srs ty))
   (where H_1 (free srs H ty β))
   (where H_2 (shrink H_1 β z))
   (side-condition (not (term (is-DST srs ty))))]

  [(free srs H (~ ty) α_0)
   H_2
   (where (ptr β) (deref H α))
   (where hv (deref H (inc α)))
   (where z (sizeof-dst srs ty hv))
   (where H_1 (free-dst srs H ty β hv))
   (where H_2 (shrink H_1 β z))
   (side-condition (term (is-DST srs ty)))]

  [(free srs H (struct s ℓs) α)
   (free-at-offsets srs H α tys zs)
   (where tys (field-tys srs s ℓs))
   (where zs (field-offsets srs s ℓs))]

  [(free srs H (Option ty) α)
   H
   (where (int 0) (deref H α))]

  [(free srs H (Option ty) α)
   (free srs H ty ,(add1 (term α)))
   (where (int 1) (deref H α))]
)

(define-metafunction Patina-machine
  lvfree : srs H V T lv -> H

  [(lvfree srs H V T lv)
   (free srs H ty α)
   (where ty (lvtype srs T lv))
   (where α (lvaddr srs H V T lv))])

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
                   ((x_0 α_0) (x_1 α_1) ...)
                   ((x_0 ty_0) (x_1 ty_1) ...))
   (shrink (free srs H_1 ty_0 α_0) α_0 z)
   (where z (sizeof srs ty_0))
   (where H_1 (free-variables srs
                              H
                              ((x_1 α_1) ...)
                              ((x_1 ty_1) ...)))])

;; this should free up all memory but that which pertains to `i` and `p`,
;; as well as `97` and `98` which are marked as 'static'
(test-equal (term (free-variables ,test-srs
                                  ,test-H
                                  ,(cadr test-V)
                                  ,(cadr test-T)))
            (term ((10 (int 22))
                   (11 (ptr 99))
                   (97 (int 29))
                   (98 (int 28))
                   (99 (int 27)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; alloc-variables -- allocate space for variables upon entry to a block,
;; filling the memory with void

(define-metafunction Patina-machine
  alloc-variables : srs H ((x : ty) ...) -> (vmap tmap H)

  [(alloc-variables srs H ()) (() () H)]
  [(alloc-variables srs H ((x_0 : ty_0) (x_1 : ty_1) ...))
   (((x_0 α_0) (x_2 α_2) ...)
    ((x_0 ty_0) (x_2 ty_2) ...)
    H_2)
   (where z (sizeof srs ty_0))
   (where (H_1 α_0) (malloc H z))
   (where (((x_2 α_2) ...)
           ((x_2 ty_2) ...)
           H_2) (alloc-variables srs H_1 ((x_1 : ty_1) ...)))])

;; this should free up all memory but that which pertains to `i` and `p`,
;; as well as `97` and `98` which are marked as 'static'
(test-equal (term (alloc-variables ,test-srs
                                   ,test-H
                                   ((j : int)
                                    (k : (struct B (static))))))
            (term (((j 100) (k 101))
                   ((j int) (k (struct B (static))))
                   ,(append (term ((102 void) (101 void) (100 void)))
                            test-H))))

;; unwrap

(define-metafunction Patina-machine
  unwrap : srs H ℓ mode ty α -> (H ty α)
  
  [(unwrap srs H ℓ (ref mq) ty α)
   (H_u ty_m α_m)
   ;; type of variable `x_m`
   (where ty_m (& ℓ mq ty))
   ;; generate memory for `x_m`
   (where (H_m α_m) (malloc H (sizeof srs ty_m)))
   ;; update mem location with ptr to payload
   (where H_u (update H_m α_m (ptr α)))]

  [(unwrap srs H ℓ move ty α)
   (H_u ty α_m)
   ;; generate memory for `x_m`
   (where (H_m α_m) (malloc H (sizeof srs ty)))
   ;; move payload from α into α_m
   (where H_u (memmove H_m α_m α (sizeof srs ty)))]
  )

(test-equal (term (unwrap ,test-srs ,test-H l1 (ref mut) (~ int)
                          ,(add1 (term (vaddr ,test-V s)))))
            (term (,(append (term [(100 (ptr 21))]) test-H)
                   (& l1 mut (~ int))
                   100)))

(test-equal (term (unwrap ,test-srs ,test-H l1 move (~ int)
                          ,(add1 (term (vaddr ,test-V s)))))
            (term (,(append (term [(100 (ptr 95))])
                            (term (deinit ,test-H 21 1)))
                   (~ int)
                   100)))

;; --> -- machine step from one configuration C to the next

(define machine-step
  (reduction-relation
   Patina-machine
   
   ;; Stack frame with no more statements. Free variables.
   [--> ((srs fns) H [vmap_0 vmap_1 ...] [tmap_0 tmap_1 ...]
         [(ℓ ()) sf_1 ...])
        ((srs fns) H_1 [vmap_1 ...] [tmap_1 ...] [sf_1 ...])
        (where H_1 (free-variables srs H vmap_0 tmap_0))]

   ;; Assignments. The memory for the lvalue should always be alloc'd,
   ;; though not always init'd.
   ;; FIXME – we need to free the old memory
   [--> ((srs fns) H V T [(ℓ ((lv = rv) st ...)) sf ...])
        ((srs fns) H_1 V T [(ℓ (st ...)) sf ...])
        (where α (lvaddr srs H V T lv))
        (where H_1 (rveval srs H V T α rv))]

   ;; Match, None case.
   [--> ((srs fns) H V T [(ℓ [st_a st ...]) sf ...])
        ((srs fns) H [() vmap ...] [() tmap ...] [(ℓ_m [bk_n]) (ℓ [st ...]) sf ...])
        ;; st_a is some kind of match:
        (where (match lv_d (Some mode x_d => bk_s) (None => bk_n)) st_a)
        ;; the discriminant lies at address α_d:
        (where α_d (lvaddr srs H V T lv_d))
        ;; it is a None value:
        (where (int 0) (deref H α_d))
        ;; generate a fresh lifetime: (FIXME)
        (where ℓ_m lmatch)
        ;; unpack V and T
        (where ([vmap ...] [tmap ...]) (V T))
        ]

   ;; Match, some case.
   [--> ((srs fns) H V T [(ℓ [st_a st ...]) sf ...])
        C_n
        ;; st_a is a match:
        (where (match lv_d (Some mode x_m => bk_s) (None => bk_n)) st_a)
        ;; the discriminant lies at address α_d:
        (where α_d (lvaddr srs H V T lv_d))
        ;; the discriminant has Option type:
        (where (Option ty) (lvtype srs T lv_d))
        ;; it is a Some value:
        (where (int 1) (deref H α_d))
        ;; make a pointer to the payload:
        (where α_v ,(add1 (term α_d)))
        ;; generate a fresh lifetime: (FIXME)
        (where ℓ_m lmatch)
        ;; handle the ref/move into `x_m`:
        (where (H_m ty_m α_m) (unwrap srs H ℓ_m mode ty α_v))
        ;; create new entry for vmap/tmap
        (where vmap_m [(x_m α_m)])
        (where tmap_m [(x_m ty_m)])
        ;; unpack V and T
        (where ([vmap ...] [tmap ...]) (V T))
        (where C_n ((srs fns) H_m [vmap_m vmap ...] [tmap_m tmap ...]
         [(ℓ_m [bk_s]) (ℓ [st ...]) sf ...]))
        ]

   ;; Push a new block.
   [--> ((srs fns) H (vmap ...) (tmap ...)
         [sf_1 sf_2 ...])
        ((srs fns) H_1  [vmap_b vmap ...] [tmap_b tmap ...]
         [sf_b (ℓ_1 [st_1 ...]) sf_2 ...])

        ;; unpack the top-most stack frame sf_1:
        (where (ℓ_1 [st_0 st_1 ...]) sf_1)
        ;; unpack the next statement st_0, which should be a block:
        (where (block ℓ_b [(x_b : ty_b) ...] [st_b ...]) st_0)
        ;; allocate space for block svariables in memory:
        (where (vmap_b tmap_b H_1) (alloc-variables srs H ((x_b : ty_b) ...)))
        ;; create new stack frame for block
        ;; FIXME substitute a fresh lifetime for ℓ_b
        (where sf_b (ℓ_b (st_b ...)))
        ]

   ;; Push a call.
   [--> ((srs fns) H V T S)
        ((srs fns) H_2 [vmap_a vmap ...] [tmap_a tmap ...]
         [(lX (bk_f)) (ℓ_1 [st_r ...]) sf_r ...])

        ;; unpack V and T for later expansion
        (where ([vmap ...] [tmap ...]) (V T))
        ;; unpack the stack frames:
        (where [(ℓ_1 sts_1) sf_r ...] S)
        ;; unpack the statements sts_1 from top-most activation:
        (where ((call g ℓs_a lvs_a) st_r ...) sts_1)
        ;; determine the types of the actual args to be passed:
        (where tys_a ,(map (λ (lv) (term (lvtype srs T ,lv)))
                           (term lvs_a)))
        ;; determine sizes of those types
        (where zs_a ,(map (λ (ty) (term (sizeof srs ,ty)))
                          (term tys_a)))
        ;; determine where lvalues are found in memory
        (where αs_a ,(map (λ (lv) (term (lvaddr srs H V T ,lv)))
                              (term lvs_a)))
        ;; lookup the fun def'n (FIXME s/ℓs_f/ℓs_a/):
        (where (fun g ℓs_f ((x_f : ty_f) ...) bk_f) (fun-defn fns g))
        ;; allocate space for parameters in memory:
        (where (vmap_a tmap_a H_1) (alloc-variables srs H ((x_f : ty_f) ...)))
        ;; determine addresses for each formal argument:
        (where βs_f ,(map (λ (lv) (term (lvaddr srs H_1
                                                        (vmap_a) (tmap_a)
                                                        ,lv)))
                             (term (x_f ...))))
        ;; move from actual params into formal params:
        (where H_2 (movemany H_1 zs_a βs_f αs_a))
        ]
   ))

;; test stepping where top-most stack frame has no remaining statements
(test--> machine-step
         (term (,twentytwo-prog () (()) (()) ((l0 ()))))
         (term (,twentytwo-prog () () () ())))

;; test popping off a stack frame with vars and another frame beneath
(test--> machine-step
         (term (,twentytwo-prog
                [(0 (int 22)) (1 (int 23))]
                [[(j 1)] [(i 0)]]
                [[(j int)] [(i int)]]
                [(l0 []) (l1 [])]))
         (term (,twentytwo-prog
                [(0 (int 22))]
                [[(i 0)]]
                [[(i int)]]
                [(l1 [])])))

;;;; test pushing a new block
(test--> machine-step
         (term (,twentytwo-prog
                [(0 (int 22))]
                [[(a 0)]]
                [[(a int)]]
                [(l1 [(block l2
                             [(b : int) (c : (~ int))]
                             [(i = 2)
                              (j = (new i))])])]))
          (term (,twentytwo-prog
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
  (term (,twentytwo-prog ,initial-H ,initial-V ,initial-T ,initial-S)))
(check-not-false (redex-match Patina-machine C state-0))

(define state-1
  (term (,twentytwo-prog
         [(2 (ptr 0)) (0 (int 0)) (1 void)]
         [[(outp 2)] [(resultp 1)]]
         [[(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(lX [(block l0 [] (((* outp) = 22)))])
          (l0 [])])))
(check-not-false (redex-match Patina-machine C state-1))

(define state-2
  (term (,twentytwo-prog
         [(2 (ptr 0)) (0 (int 0)) (1 void)]
         [[] [(outp 2)] [(resultp 1)]]
         [[] [(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(l0 [((* outp) = 22)])
          (lX [])
          (l0 [])])))
(check-not-false (redex-match Patina-machine C state-2))

(define state-3
  (term (,twentytwo-prog
         [(2 (ptr 0)) (0 (int 22)) (1 void)]
         [[] [(outp 2)] [(resultp 1)]]
         [[] [(outp (& a mut int))] [(resultp (& l0 mut int))]]
         [(l0 [])
          (lX [])
          (l0 [])])))
(check-not-false (redex-match Patina-machine C state-3))

(define state-N
  (term (,twentytwo-prog
         [(0 (int 22))]
         []
         []
         [])))
(check-not-false (redex-match Patina-machine C state-N))

(test--> machine-step state-0 state-1)
(test--> machine-step state-1 state-2)
(test--> machine-step state-2 state-3)
(test-->> machine-step state-0 state-N)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; test summation example

(define sum-state-0
  (term (,sum-prog ,initial-H ,initial-V ,initial-T ,initial-S)))
(check-not-false (redex-match Patina-machine C sum-state-0))

(define sum-state-N
  (term (,sum-prog [(0 (int 66))] [] [] [])))
(check-not-false (redex-match Patina-machine C sum-state-N))

(test-->> machine-step sum-state-0 sum-state-N)
