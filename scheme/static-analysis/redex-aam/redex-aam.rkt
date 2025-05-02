#lang racket

(require redex)
;(require "shared.rkt")

;; Warmup

(define-language L
  (M ::= N F (M ...))
  (F ::= fred wilma)
  (N ::= 2 7))

(test-equal (redex-match? L N (term 2)) #t)

(test-equal (redex-match? L N (term 9)) #f)

(test-equal (redex-match? L N (term fred)) #f)

(test-equal (redex-match? L M (term (((((fred))))))) #t)

(test-equal (redex-match? L M (term ())) #t)

(test-equal (redex-match? L M (term (fred 2 (wilma)))) #t)

(test-equal (redex-match? L (N ...) (term 2)) #f)

(test-equal (redex-match? L (N ...) (term (7 2 7))) #t)

(test-equal (redex-match? L (M_1 M_2) (term (7 (2 fred)))) #t)

(test-equal (redex-match? L (M M) (term ((2 fred) (2 fred)))) #t)

(test-equal (redex-match? L (M M) (term ((2 fred) (7 fred)))) #f)

(define-metafunction L
  swap : M -> M
  [(swap fred) wilma]
  [(swap wilma) fred]
  [(swap (M ...)) ((swap M) ...)]
  [(swap M) M])

(test-equal (term (swap (wilma fred))) '(fred wilma))

(test-equal (term (7 (swap (wilma 2 (fred))))) '(7 (fred 2 (wilma))))

;; PCF

; Values: natural numbers, functions, and primitive operations
; Terms: variables, values, applications, conditionals, recursive functions

(define-language PCF
  (M ::=
     N O X L
     (μ (X : T) L)
     (M M ...)
     (if0 M M M))
  (X ::= variable-not-otherwise-mentioned)
  (L ::= (λ ([X : T] ...) M))
  (V ::= N O L)
  (N ::= number)
  (O ::= O1 O2)
  (O1 ::= add1 sub1)
  (O2 ::= + *)
  (T ::= num (T ... -> T)))

(define-term fact-5
  ((μ (fact : (num -> num))
      (λ ([n : num])
        (if0 n
             1
             (* n (fact (sub1 n))))))
   5))

(test-equal (redex-match? PCF M (term fact-5)) #t)

;; Typing judgement

(define-extended-language PCFT PCF
  (Γ ::= ((X T) ...)))

(define-language REDEX)

(define-judgment-form REDEX
  #:mode (lookup I I O)
  #:contract (lookup ((any any) ...) any any)
  [(lookup (_ ... (any any_0) _ ...) any any_0)])

(test-equal (judgment-holds (lookup ((x 1) (y 2) (x 3)) x 1))
            #t)

(test-equal (judgment-holds (lookup ((x 1) (y 2) (x 3)) x 2))
            #f)

(test-equal (judgment-holds (lookup ((x 1) (y 2) (x 3)) x 3))
            #t)

(test-equal (judgment-holds (lookup ((x 1) (y 2) (x 3)) x any) any)
            '(1 3))

(define-metafunction REDEX
  ext1 : ((any any) ...) (any any) -> ((any any) ...)
  [(ext1 (any_0 ... (any_k any_v0) any_1 ...) (any_k any_v1))
   (any_0 ... (any_k any_v1) any_1 ...)]
  [(ext1 (any_0 ...) (any_k any_v1))
   ((any_k any_v1) any_0 ...)])

(define-metafunction REDEX
  ext : ((any any) ...) (any any) ... -> ((any any) ...)
  [(ext any) any]
  [(ext any any_0 any_1 ...)
   (ext1 (ext any any_1 ...) any_0)])

; any_!_1 ... matches disjoint sequences.
#|
(define-metafunction REDEX
  unique : any ... -> boolean
  [(unique any_!_1 ...) #t]
  [(unique _ ...) #f])
|#

; short hand for defining predicates
(define-relation REDEX
  unique ⊆ (any ...)
  [(unique any_!_1 ...)])

(test-equal (term (unique)) #t)

(test-equal (term (unique 1)) #t)

(test-equal (term (unique 1 2 1)) #f)

; define-judement-form defines a relation.

; A relation in Redex is a function from inputs to sets of outputs,
;  and the definition of relation ust specify which positions of
;  the relation are inputs and which are outputs, as seen in #:mode.
; The #:contract specifies the signature of the relation.

; The two real inputs are type environment and term, the output is
;  the type.
(define-judgment-form PCFT
  #:mode (⊢ I I I O)
  #:contract (⊢ Γ M : T)
  [(lookup Γ X T)
   -------------- var
   (⊢ Γ X : T)]
  [------------- num
   (⊢ Γ N : num)]
  [----------------------- op1
   (⊢ Γ O1 : (num -> num))]
  [--------------------------- op2
   (⊢ Γ O2 : (num num -> num))]
  [(⊢ Γ M_1 : num)
   (⊢ Γ M_2 : T)
   (⊢ Γ M_3 : T)
   ------------------------- if0
   (⊢ Γ (if0 M_1 M_2 M_3) : T)]
  [(⊢ (ext Γ (X T)) L : T)
   ---------------------- μ
   (⊢ Γ (μ (X : T) L) : T)]
  [(⊢ Γ M_0 : (T_1 ..._1 -> T))
   (⊢ Γ M_1 : T_1) ...
   ------------------------ app
   (⊢ Γ (M_0 M_1 ..._1) : T)]
  [(unique X ...)
   (⊢ (ext Γ (X T) ...) M : T_n)
   ------------------------------------------ λ
   (⊢ Γ (λ ([X : T] ...) M) : (T ... -> T_n))])

(test-equal (judgment-holds (⊢ () (λ ([x : num]) x) : (num -> num)))
            #t)

(test-equal (judgment-holds (⊢ () (λ ([x : num]) x) : T) T)
            '((num -> num)))

(test-equal (judgment-holds (⊢ () fact-5 : T) T)
            '(num))

#|
(show-derivations
 (build-derivations
  (⊢ () (λ ([x : num]) (add1 x)) : T)))
|#

; ill-formed lambda-abstractions have no type
(test-equal (judgment-holds (⊢ () (λ ([x : num] [x : num]) x) : T) T)
            '())

;; The calculus of PCF

(define r
  (reduction-relation
   PCF #:domain M
   (--> (μ (X : T) M)
        (subst (X (μ (X : T) M)) M)
        μ)

   (--> ((λ ([X : T] ...) M_0) M ...)
        (subst (X M) ... M_0)
        β)

   (--> (O N_0 ...) N_1
        (judgment-holds (δ (O N_0 ...) N_1))
        δ)

   (--> (if0 0 M_1 M_2) M_1 if-t)
   (--> (if0 N M_1 M_2) M_2
        (side-condition (not (zero? (term N))))
        if-f)))

(define-judgment-form PCF
  #:mode (δ I O)
  #:contract (δ (O N ...) N)
  [(δ (+ N_0 N_1) ,(+ (term N_0) (term N_1)))]
  [(δ (* N_0 N_1) ,(* (term N_0) (term N_1)))]
  [(δ (sub1 N) ,(sub1 (term N)))]
  [(δ (add1 N) ,(add1 (term N)))])

(test-equal (term (subst (x 5) (y 7) (+ x y))) '(+ 5 7))

(test-equal (apply-reduction-relation r (term (add1 5)))
            '(6))

; only takes one step of computation
(test-equal (apply-reduction-relation r (term ((λ ([x : num]) x) (add1 5))))
            '((add1 5)))

; the reduction only occurs at the outermost term
(test-equal (apply-reduction-relation r (term (sub1 ((λ ([x : num]) x) (add1 5)))))
            '())

; take any number of steps and return the set of irreducible terms
(test-equal (apply-reduction-relation* r (term (add1 5)))
            '(6))

(test-equal (apply-reduction-relation* r (term ((λ ([x : num]) x) (add1 5))))
            '(6))

(test-equal (apply-reduction-relation* r (term (sub1 ((λ ([x : num]) x) (add1 5)))))
            '((sub1 ((λ ((x : num)) x) (add1 5)))))

; compatible relation
(define -->r (compatible-closure r PCF M))

(test-equal (apply-reduction-relation* -->r (term ((λ ([x : num]) x) (add1 5))))
            '(6))

(test-equal (apply-reduction-relation* -->r (term (sub1 ((λ ([x : num]) x) (add1 5)))))
            '(5))

; visualize the reductions
;(traces -->r (term ((λ ([x : num]) x) (add1 5))))

;; Call-by-name

(define-extended-language PCFn PCF
  (E ::= hole
     (E M ...)
     (O V ... E M ...)
     (if0 E M M)))

; left-most, outer-most call-by-name reduction
(define -->n (context-closure r PCFn E))

(test-equal (apply-reduction-relation* -->n (term ((λ ([x : num]) x) (add1 5))))
            '(6))

;(traces -->n (term ((λ ([x : num]) x) (add1 5))))

(test-equal (apply-reduction-relation* -->n (term fact-5))
            '(120))

; or using test-->>
(test-->> -->n (term fact-5) 120)

; using test-->>∃ for testing reachability
(test-->>∃ -->r (term fact-5) 120)

;; Call-by-value

(define-extended-language PCFv PCF
  (E ::= hole
     (V ... E M ...)
     (if0 E M M)))

; overwriting beta rule of r
(define v
  (extend-reduction-relation
   r PCF #:domain M
   (--> ((λ ([X : T] ...) M_0) V ...)
        (subst (X V) ... M_0)
        β)))

(define -->v (context-closure v PCFv E))

;(traces -->v (term ((λ ([x : num]) x) (add1 5))))

(test-equal (apply-reduction-relation* -->v (term fact-5))
            '(120))

(define-term Ω
  ((μ (loop : (num -> num))
      (λ ([x : num])
        (loop x)))
   0))

(test-equal (apply-reduction-relation* -->n (term ((λ ([x : num]) 0) Ω)))
            '(0))

(test-equal (apply-reduction-relation* -->v (term ((λ ([x : num]) 0) Ω)))
            '())

;; Evaluation

(define-extended-language PCF⇓ PCF
  (V ::= N O (L ρ) ((μ (X : T) L) ρ))
  (ρ ::= ((X V) ...)))

;evaluation function ⇓
(define-judgment-form PCF⇓
  #:mode (⇓ I I I O)
  #:contract (⇓ M ρ : V)

  [(⇓ N ρ : N)]
  [(⇓ O ρ : O)]
  [(⇓ L ρ : (L ρ))]
  [(⇓ (μ (X_f : T_f) L) ρ : ((μ (X_f : T_f) L) ρ))]

  [(lookup ρ X V)
   --------------
   (⇓ X ρ : V)]

  [(⇓ M_0 ρ : N)
   (where M ,(if (zero? (term N)) (term M_1) (term M_2)))
   (⇓ M ρ : V)
   --------------------
   (⇓ (if0 M_0 M_1 M_2) ρ : V)]

  [(⇓ M_0 ρ : O)
   (⇓ M_1 ρ : N)
   ...
   (δ (O N ...) N_1)
   --------------------
   (⇓ (M_0 M_1 ...) ρ : N_1)]

  [(⇓ M_0 ρ : ((λ ([X_1 : T] ...) M) ρ_1))
   (⇓ M_1 ρ : V_1)
   ...
   (⇓ M (ext ρ_1 (X_1 V_1) ...) : V)
   ---------------------------------
   (⇓ (M_0 M_1 ...) ρ : V)]

  [(⇓ M_0 ρ : (name f ((μ (X_f : T_f) (λ ([X_1 : T] ...) M)) ρ_1)))
   (⇓ M_1 ρ : V_1)
   ...
   (⇓ M (ext ρ_1 (X_f f) (X_1 V_1) ...) : V)
   -----------------------------------------
   (⇓ (M_0 M_1 ...) ρ : V)])

(test-equal (judgment-holds (⇓ fact-5 () : V) V) '(120))

(test-equal (judgment-holds (⇓ fact-5 () : 120)) #t)