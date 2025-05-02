#lang typed/racket
;; Denotational semantics for Contract PCF

;; SYNTAX
;; ======
;;
;; E = (vbl X)
;;   | (app E E)
;;   | (if E E E)
;;   | (lam X E)
;;   | (num N)
;;   | (mon C E L L L)
;;   | (prim O)
;;   | (bool B)
;;
;; C = (pred E)
;;   | (~> C C)
;;
;; X = Symbol
;; L = Symbol

;; SEMANTICS
;; =========
;;
;; V = N | O | B
;;   | (clo E R)
;;   | (arr D D V)
;; 
;; O = '+ | '-
;;   | (plus N) 
;;   | (minus N)
;;
;; D = (--> D D)
;;   | (flat V L L)

;; Ans = (ret V Σ)
;;     | (blame L L)

;; Dns = (dret D Σ)
;;     | (blame L L)

(define-type C (U pred ~>))
(define-type D (U flat -->))
(define-type E (U app lam vbl num mon prim bool ife))
(define-type R (Listof (Pair X A)))
(define-type Σ (Listof (Pair A V)))
(define-type V (U N B O clo arr prim))
(define-type N Integer)
(define-type O (U '+ '- plus minus
                  'even? 'odd?))
(define-type A Symbol) ;; Addresses
(define-type X Symbol) ;; Variables
(define-type L Symbol) ;; Labels
(define-type B Boolean)
(define-type Ans (U ret blame))
(define-type Dns (U dret blame))

(struct: app   ([e0 : E]  [e1 : E])         #:transparent)
(struct: lam   ([x  : X]  [e  : E])         #:transparent)
(struct: vbl   ([x  : X])                   #:transparent)
(struct: num   ([n  : N])                   #:transparent)
(struct: mon   ([c  : C]  
                [e  : E]
                [p  : L]
                [n  : L]
                [s  : L])                   #:transparent)
(struct: prim  ([o  : O])                   #:transparent)
(struct: ~>    ([c1 : C] [c2 : C])          #:transparent)
(struct: pred  ([e  : E])                   #:transparent)
(struct: bool  ([b  : B])                   #:transparent)
(struct: ife   ([e0 : E] [e1 : E] [e2 : E]) #:transparent)

(struct: -->   ([d1 : D] [d2 : D])          #:transparent)
(struct: flat  ([v  : V] [p  : L] [s : L])  #:transparent)

(struct: blame ([l1 : L] [l2 : L])          #:transparent)
(struct: clo   ([e  : E] [ρ  : R])          #:transparent)
(struct: ret   ([v  : V] [σ  : Σ])          #:transparent)
(struct: dret  ([d  : D] [σ  : Σ])          #:transparent)
(struct: arr   ([d0 : D] [d1 : D] [v : V])  #:transparent)
(struct: plus  ([n  : N])                   #:transparent)
(struct: minus ([n  : N])                   #:transparent)

(: parse (Any -> E))
(define (parse sexp)
  (match sexp    
    ['+ (prim '+)]
    ['- (prim '-)]
    ['even? (prim 'even?)]
    ['odd? (prim 'odd?)]
    [(? symbol? x) (vbl x)]
    [(? exact-integer? n) (num n)]
    [(? boolean? b) (bool b)]
    [(list 'if e1 e2 e3)
     (ife (parse e1)
          (parse e2)
          (parse e3))]
    [(list '=> c e)
     (define l (gensym))
     (define pos (symbol+ '+: l))
     (define neg (symbol+ '-: l))
     (mon (parse-con c) (parse e) pos neg pos)]
    [(list 'λ (list (? symbol? x)) e)
     (lam x (parse e))]
    [(list e1 e2)
     (app (parse e1) (parse e2))]
    [_ (error "Unkown sexp")]))

(: parse-con (Any -> C))
(define (parse-con sexp)
  (match sexp
    [(list '-> c1 c2)
     (~> (parse-con c1) (parse-con c2))]
    [e (pred (parse e))]))

(: ev (E R Σ -> Ans))
(define (ev e ρ σ)
  (match e
    [(lam x e) (ret (clo (lam x e) ρ) σ)]
    [(vbl x)   (ret (lookup σ ρ x) σ)]
    [(num n)   (ret n σ)]
    [(prim o)  (ret o σ)]
    [(bool b)  (ret b σ)]
    [(app e0 e1)
     (match (ev e0 ρ σ)
       [(? blame? b) b]
       [(ret v1 σ1) 
        (match (ev e1 ρ σ1)
          [(? blame? b) b]
          [(ret v2 σ2)
           (apply v1 v2 σ2)])])]
    [(ife e0 e1 e2)
     (match (ev e0 ρ σ)
       [(? blame? b) b]
       [(ret #f σ1)  (ev e2 ρ σ1)]
       [(ret v σ1)   (ev e1 ρ σ1)])]
    [(mon c e p n s)
     (match (ev e ρ σ)
       [(ret v1 σ)
        (match (cv c ρ σ p n s)
          [(dret d σ) 
           (monitor d v1 σ)])])]))

(: cv (C R Σ L L L -> Dns))
(define (cv c ρ σ p n s)
  (match c
    [(~> c1 c2)
     (match (cv c1 ρ σ p n s)
       [(dret d1 σ1)
        (match (cv c2 ρ σ1 n p s)
          [(dret d2 σ2)
           (dret (--> d1 d2) σ2)])])]
    [(pred e) 
     (match (ev e ρ σ)
       [(? blame? b) b]
       [(ret v σ) (dret (flat v p s) σ)])]))

(: apply (V V Σ -> Ans))
(define (apply f v σ)
  (match f
    [(arr d1 d2 f)
     (match (monitor d1 v σ)
       [(? blame? b) b]
       [(ret v1 σ1)
        (match (apply f v1 σ1)
          [(ret v2 σ2)
           (monitor d2 v2 σ2)])])]
    ['+
     (match v
       [(? number? n) (ret (plus n) σ)])]
    ['-
     (match v
       [(? number? n) (ret (minus n) σ)])]
    [(plus n)
     (match v
       [(? number? m)
        (ret (+ m n) σ)])]
    [(minus n)
     (match v
       [(? number? m)
        (ret (- m n) σ)])]
    ['even?
     (match v
       [(? number? n)
        (ret (even? n) σ)])]
    ['odd?
     (match v
       [(? number? n)
        (ret (odd? n) σ)])]
    [(clo (lam x e) ρ)
     (define a (alloc))
     (ev e 
         (extend-env ρ x a)
         (extend-sto σ a v))]))


(: monitor (D V Σ -> Ans))
(define (monitor d v σ)
  (match d
    [(--> d1 d2)
     (ret (arr d1 d2 v) σ)]
    [(flat f p s)
     (match (apply f v σ)
       [(? blame? b) b]
       [(ret #t σ) (ret v σ)]
       [(ret #f σ) (blame p s)])]))

(: lookup (Σ R X -> V))
(define (lookup σ ρ x)
  (define xa ((inst assoc X A) x ρ))
  (if xa
      (let ()
        (define av ((inst assoc A V) (cdr xa) σ))
        (if av 
            (cdr av)
            (error "Unbound address")))
      (error "Unbound variable")))

(: extend-env (R X A -> R))
(define (extend-env ρ x a)
  ((inst cons (Pair X A) R) 
   ((inst cons X A) x a) ρ))

(: extend-sto (Σ A V -> Σ))
(define (extend-sto σ a v)
  ((inst cons (Pair A V) Σ) 
   ((inst cons A V) a v) σ))
  

(define (alloc) (gensym))

(: symbol+ (Symbol Symbol -> Symbol))
(define (symbol+ s1 s2) 
  (string->symbol (string-append (symbol->string s1)
                                 (symbol->string s2))))

(: run (Any -> Ans))
(define (run sexp)
  (ev (parse sexp) empty empty))

(run '5)
(run '+)
(run '(λ (x) 4))
(run '((λ (x) 4) 5))
(run '((λ (x) x) 5))
(run '(if 0 1 2))
(run '(if #f 1 2))
(run '(+ 5))
(run '((+ 5) 6))
(run '((- 5) 6))
(run '(even? 5))
(run '(odd? 5))
(run '(=> odd? 5))
(run '(=> even? 5))
(run '(=> (-> even? even?) (λ (x) x)))
(run '(=> (λ (_) #t) 7))
(run '(=> (-> (λ (_) #t) (λ (_) #t)) (λ (x) x)))
(run '((=> (-> (λ (y) #t) (λ (z) #t)) (λ (x) x)) 6))
(run '((=> (-> (λ (y) #f) (λ (z) #t)) (λ (x) x)) 6))
(run '((=> (-> (λ (y) #t) (λ (z) #f)) (λ (x) x)) 6))
