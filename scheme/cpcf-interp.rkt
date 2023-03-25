#lang typed/racket

;; An interpreter semantics for CPCF
;; A reconstruction based on https://gist.github.com/dvanhorn/3041667

;; XXX:
; flat has two labels?
; blame takes two labels?

;; Syntax

(define-type Label Symbol)
(define-type Num Integer)
(define-type Var Symbol)
(define-type Op (U '+1 '-1 'even? 'odd? 'zero?))

; Expressions
(define-type Expr
  (U app lam vbl num mon prim bool ite))
; Contract
(define-type Contract (U pred ~>))
; Polarity
(define-type Party (U ':server ':client))

(struct: app ([e0 : Expr] [e1 : Expr]) #:transparent)
(struct: lam ([x : Symbol] [e : Expr]) #:transparent)
(struct: vbl ([x : Var]) #:transparent)
(struct: num ([n : Num]) #:transparent)
(struct: mon ([c : Contract] [p : Party] [e : Expr] [l : Label]) #:transparent)
(struct: prim ([op : Op]) #:transparent)
(struct: bool ([b : Boolean]) #:transparent)
(struct: ite ([c : Expr] [thn : Expr] [els : Expr]) #:transparent)

(struct: pred ([e : Expr]) #:transparent)
(struct: ~> ([c1 : Contract] [c2 : Contract]) #:transparent)

;; Semantics

(define-type Kon (U flat -->))
(struct: flat ([v : Value] [l : Label] [p : Party]) #:transparent)
(struct: --> ([c0 : Kon] [c1 : Kon]) #:transparent)

(define-type Value (U Num Boolean Op clo arr))
; ordinary function value
(struct: clo ([e : Expr] [ρ : Env]) #:transparent)
; function value guarded by a contract
(struct: arr ([d0 : Kon] [d1 : Kon] [v : Value]) #:transparent)

(define-type Addr Symbol)
(define-type Env (Listof (Pair Var Addr)))
(define-type Sto (Listof (Pair Addr Value)))

(define-type Ans (U ret blame))
(struct: ret ([v : Value] [σ : Sto]) #:transparent)
(struct: blame ([l : Label]) #:transparent)

(define-type MAns (U mret blame))
(struct: mret ([c : Kon] [σ : Sto]) #:transparent)

(: lookup (Env Sto Var -> Value))
(define (lookup ρ σ x)
  (define xa ((inst assoc Var Addr) x ρ))
  (if xa
      (let ()
        (define av ((inst assoc Addr Value) (cdr xa) σ))
        (if av 
            (cdr av)
            (error "Unbound address")))
      (error "Unbound variable")))

(: symbol+ (Symbol Symbol -> Symbol))
(define (symbol+ s1 s2) 
  (string->symbol (string-append (symbol->string s1)
                                 (symbol->string s2))))

(: neg (Party -> Party))
(define (neg p)
  (match p
    [':server ':client]
    [':client ':server]))

(: extend-env (Env Var Addr -> Env))
(define (extend-env ρ x a)
  ((inst cons (Pair Var Addr) Env) 
   ((inst cons Var Addr) x a) ρ))

(: extend-sto (Sto Addr Value -> Sto))
(define (extend-sto σ a v)
  ((inst cons (Pair Addr Value) Sto) 
   ((inst cons Addr Value) a v) σ))

(define (alloc) (gensym))

(: apply (Value Value Sto -> Ans))
(define (apply f v σ)
  (match f
    [(arr k1 k2 f)
     (match (monitor k1 v σ)
       [(? blame? b) b]
       [(ret v1 σ1)
        (match (apply f v1 σ1)
          [(? blame? b) b]
          [(ret v2 σ2)
           (monitor k2 v2 σ2)])])]
    [(clo (lam x e) ρ)
     (define a (alloc))
     (eval e (extend-env ρ x a) (extend-sto σ a v))]
    ['+1
     (match v
       [(? number? n) (ret (+ v 1) σ)])]
    ['-1
     (match v
       [(? number? n) (ret (- v 1) σ)])]
    ['zero?
     (match v
       [(? number? n) (ret (eq? n 0) σ)])]
    ['even?
     (match v
       [(? number? n) (ret (even? n) σ)])]
    ['odd?
     (match v
       [(? number? n) (ret (odd? n) σ)])]))

(: monitor (Kon Value Sto -> Ans))
(define (monitor k v σ)
  (match k
    [(flat f l p)
     (match (apply f v σ)
       [(? blame? b) b]
       [(ret #t σ) (ret v σ)]
       [(ret #f σ) (blame (symbol+ l p))])]
    [(--> k1 k2)
     (ret (arr k1 k2 v) σ)]))

(: eval-contract (Contract Env Sto Label Party -> MAns))
(define (eval-contract c ρ σ l p)
  (match c
    [(~> c1 c2)
     (match (eval-contract c1 ρ σ l (neg p))
       [(mret d1 σ1)
        (match (eval-contract c2 ρ σ1 l p)
          [(mret d2 σ2)
           (mret (--> d1 d2) σ2)])])]
    [(pred e)
     (match (eval e ρ σ)
       [(? blame? b) b]
       [(ret v σ) (mret (flat v l p) σ)])]))

(: eval (Expr Env Sto -> Ans))
(define (eval e ρ σ)
  (match e
    [(num n) (ret n σ)]
    [(prim o) (ret o σ)]
    [(bool b)  (ret b σ)]
    [(vbl x) (ret (lookup ρ σ x) σ)]
    [(lam x e) (ret (clo (lam x e) ρ) σ)]
    [(app e0 e1)
     (match (eval e0 ρ σ)
       [(? blame? b) b]
       [(ret v0 σ0)
        (match (eval e1 ρ σ0)
          [(? blame? b) b]
          [(ret v1 σ1)
           (apply v0 v1 σ1)])])]
    [(ite e1 e2 e3)
     (match (eval e1 ρ σ)
       [(? blame? b) b]
       [(ret #f σ1) (eval e3 ρ σ1)]
       [(ret v  σ1) (eval e2 ρ σ1)])]
    [(mon c p e l)
     (match (eval e ρ σ)
       [(ret v σ1)
        (match (eval-contract c ρ σ l p)
          [(mret k σ2)
           (monitor k v σ2)])])]))

(: eval-top (Expr -> Ans))
(define (eval-top e)
  (eval e '() '()))

;; Examples

; Ok
(eval-top
 (app
  (lam 'x (app (prim '+1) (vbl 'x)))
  (num 3)))

; Ok
(eval-top
 (app
  (lam 'x (app (prim '+1) (vbl 'x)))
  (mon (pred (lam 'x (app (prim 'odd?) (vbl 'x))))
       ':server
       (num 3)
       'l0)))

; Blame argument a0
(eval-top
 (app
  (lam 'x (app (prim '+1) (vbl 'x)))
  (mon (pred (lam 'x (app (prim 'even?) (vbl 'x))))
       ':server
       (num 3)
       'a0)))

; Blame f's argument/context
(eval-top
 (app
  (mon (~> (pred (lam 'x (app (prim 'odd?) (vbl 'x))))
           (pred (lam 'x (app (prim 'odd?) (vbl 'x)))))
       ':server
       (lam 'x (vbl 'x))
       'f0)
  (num 4)))

; Blame f's implementation
(eval-top
 (app
  (mon (~> (pred (lam 'x (app (prim 'odd?) (vbl 'x))))
           (pred (lam 'x (app (prim 'even?) (vbl 'x)))))
       ':server
       (lam 'x (vbl 'x))
       'f0)
  (num 3)))

; Ok
(eval-top
  (app
   (mon (~> (pred (lam 'x (app (prim 'odd?) (vbl 'x))))
            (pred (lam 'x (app (prim 'even?) (vbl 'x)))))
        ':server
        (lam 'x (app (prim '+1) (vbl 'x)))
        'f0)
   (num 3)))

; Blame the result of application (v0:server)
(eval-top
 (mon
  (pred (prim 'odd?))
  ':server
  (app
   (mon (~> (pred (lam 'x (app (prim 'odd?) (vbl 'x))))
            (pred (lam 'x (app (prim 'even?) (vbl 'x)))))
        ':server
        (lam 'x (app (prim '+1) (vbl 'x)))
        'f0)
   (num 3))
  'v0))

; Sec 3.2 example from Dimoulas & Felleisen TOPLAS
; Blame the server since

(define serM
  (lam 'f
       (ite (app (prim 'zero?) (app (vbl 'f) (num 1)))
            (vbl 'f)
            (vbl 'f))))

; Blame f0's client, since it doesn't provide a good (function) value to f0
(eval-top
 (app
  (app
   (mon (~> (~> (pred (prim 'odd?))
                (pred (prim 'odd?)))
            (~> (pred (lam 'x (bool #t)))
                (pred (lam 'x (bool #t)))))
        ':server
        serM
        'f0)
   (lam 'y (app (prim '+1) (vbl 'y))))
  (num 1)))

; Blame f0 server
(eval-top
 (app
  (app
   (mon (~> (~> (pred (prim 'odd?))
                (pred (prim 'odd?)))
            (~> (pred (lam 'x (bool #t)))
                (pred (lam 'x (bool #t)))))
        ':server
        serM
        'f0)
   (lam 'y (vbl 'y)))
  (num 2))) ; Ok if the returned function is only applied with odd numbers

; Observe that the returned function has two layers function contract
(eval-top
 (app
   (mon (~> (~> (pred (prim 'odd?))
                (pred (prim 'odd?)))
            (~> (pred (lam 'x (bool #t)))
                (pred (lam 'x (bool #t)))))
        ':server
        serM
        'f0)
   (lam 'y (vbl 'y))))
