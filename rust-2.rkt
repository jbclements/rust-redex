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
      bk)
  ;; lvalues :
  ;; changing "field names" to be numbers
  (lv x (lv : f) (* lv))
  ;; rvalues :
  (rv (copy lv)                    ;; copy lvalue
      (& l mq lv)                  ;; take address of lvalue
      (move lv)                    ;; move lvalue
      (struct s (l ...) (f x) ...) ;; struct constant
      (new x)                      ;; allocate memory
      number                       ;; constant number
      (+ x x)                      ;; sum
      )
  ;; types : 
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
  [sf (vmaps tmaps bas)]
  ;; vmaps: maps variable names to addresses
  [vmaps (vmap ...)]
  [vmap ((x alpha) ...)]
  ;; tmaps : a map from names to types
  [tmaps (tmap ...)]
  [tmap ((x ty) ...)]
  ;; S (stack) : a list of block frames
  [bas ((ba bas) ...)]
  ;; ba (block activation) : a label and a list of statements
  [ba (l sts)]
  [sts (st ...)]
  [(alpha beta) number])

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

;; vaddr -- lookup addr of variable in vmaps
 
(define-metafunction Patina-machine
  vaddr : vmaps x -> alpha
  
  [(vaddr vmaps x_0)
   ,(get* (term x_0) (term vmaps))])
         
(test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) a))
            (term 0))
(test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) b))
            (term 1))
(test-equal (term (vaddr (((a 0) (b 1)) ((c 2))) c))
            (term 2))

;; vtype -- lookup type of variable in vmaps
 
(define-metafunction Patina-machine
  vtype : tmaps x -> ty
  
  [(vtype tmaps x_0)
   ,(get* (term x_0) (term tmaps))])

(define test-vtypes (term (((a int) (b (~ int))) ((c (struct-ty A ()))))))

(test-equal (term (vtype ,test-vtypes a)) (term int))

(test-equal (term (vtype ,test-vtypes c)) (term (struct-ty A ())))

;; struct-tys

(define-metafunction Patina-machine
  struct-tys : srs s ls -> (ty ...)
  
  [(struct-tys ((struct s_0 (l_0 ...) (ty_0 ...)) sr ...) s_0 ls_1)
   (ty_0 ...)] ;; XXX subst lifetimes

  [(struct-tys ((struct s_0 (l_0 ...) (ty_0 ...)) sr ...) s_1 ls_1)
   (struct-tys (sr ...) s_1 ls_1)])

(define test-structs
  (term [(struct A () (int))
         (struct B (l0) (int (& l0 mut int)))
         (struct C (l0) ((struct-ty A ())
                         (struct-ty B (l0))))
         (struct D (l0) ((struct-ty C (l0))
                         (struct-ty A ())
                         (struct-ty C (l0))
                         (struct-ty B (l0))))
         ]))

(test-equal (term (struct-tys ,test-structs A ()))
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

(test-equal (term (sizeof ,test-structs (struct-ty A ())))
            (term 1))

(test-equal (term (sizeof ,test-structs (struct-ty B (static))))
            (term 2))

(test-equal (term (sizeof ,test-structs (struct-ty C (static))))
            (term 3))

;; offsetof

(define-metafunction Patina-machine
  offsetof : srs s ls f -> number
  
  [(offsetof srs s ls f)
   ,(foldl + 0 (map (lambda (t) (term (sizeof srs ,t)))
                    (take (term (struct-tys srs s ls))
                          (term f))))])

(test-equal (term (offsetof ,test-structs C (static) 0))
            (term 0))

(test-equal (term (offsetof ,test-structs C (static) 1))
            (term 1))

(test-equal (term (offsetof ,test-structs D (static) 1))
            (term 3))

(test-equal (term (offsetof ,test-structs D (static) 3))
            (term 7))

;; lvtype -- compute type of an lvalue

(define-metafunction Patina-machine
  dereftype : ty -> ty
  
  [(dereftype (~ ty)) ty]
  [(dereftype (& l mq ty)) ty])

(define-metafunction Patina-machine
  fieldtype : srs ty f -> ty
  
  [(fieldtype srs (struct-ty s ls) f)
   (car (drop (struct-tys srs s ls) f))]) ; fixme--surely a better way

(define-metafunction Patina-machine
  lvtype : srs tmaps lv -> ty
  
  [(lvtype tmaps x)
   (vtype tmaps x)]
  
  [(lvtype tmaps (* lv))
   (dereftype (lvtype tmaps lv))]
  
  [(lvtype tmaps (lv : f))
   (fieldtype (lvtype tmaps lv) f)])

(check-equal (term (lvtype test-structs test-

;; addr -- lookup addr of variable in vmaps

;(define-metafunction Patina-machine
;  addr : srs H vmaps tmaps lv -> alpha
;  
;  [(addr srs H vmaps tmaps x)
;   (vaddr vmaps x)]
;  
;  [(addr srs H vmaps tmaps (* lv))
;  (deref H (addr H vmaps lv))]
;  
;  [(addr srs H vmaps tmaps (lv : f))
;   ,(+ (addr srs H vmaps lv)
;       (offsetof srs 