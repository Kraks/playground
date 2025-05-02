#lang racket

;; Chapter 6
;; Typed NbE

(require rackunit)
(require "error.rkt")

(struct ZERO () #:transparent)
(struct ADD1 (pred) #:transparent)
(struct NEU (type neu) #:transparent)
(struct N-var (name) #:transparent)
(struct N-ap (rator rand) #:transparent)
(struct N-rec (type target base step) #:transparent)

(struct THE (type value) #:transparent) ;; normal forms

(struct CLOS (env var body) #:transparent)

(define (norm? v)
  (THE? v))

(define (extend ρ x v)
  (cons (cons x v) ρ))

(define (add-* x)
  (string->symbol (string-append (symbol->string x) "*")))

(define (freshen used x)
  (if (memv x used)
      (freshen used (add-* x))
      x))

#| Bidirectional Type Checking |#

#|
Two mode:
  checking, an expression is analyzed against a known type to see if it fits;
  synthesis, a type is derived directly from an expression.
Split the judgement Γ ⊢ e : t to two forms of judgement:
  Γ ⊢ e ⇒ t, meaning that type t can be synthesized from e (on eliminations)
  Γ ⊢ e ⇐ t, meaning that it is possible to check e has type t (on introductions)
|#

(define (type=? t1 t2)
  (match* (t1 t2)
    [('Nat 'Nat) #t]
    [(`(→ ,A1 ,B1) `(→ ,A2 ,B2))
     (and (type=? A1 A2) (type=? B1 B2))]
    [(_ _) #f]))

(define (type? t)
  (type=? t t))

(check-true (type? 'Nat))
(check-false (type? '(Nat)))
(check-true (type? '(→ Nat Nat)))
(check-true (type=? '(→ Nat (→ Nat Nat))
                    '(→ Nat (→ Nat Nat))))
(check-false (type=? '(→ (→ Nat Nat) Nat)
                     '(→ Nat (→ Nat Nat))))

(define (synth Γ e)
  (match e
    ; Type annotations
    [`(the ,t ,e2)
     (if (not (type? t))
         (stop e (format "Invalid type ~a" t))
         (go-on ([_ (check Γ e2 t)])
                (go t)))]
    ; Recursion on nat
    [`(rec ,tp ,tgt ,base ,step)
     (go-on ([tgt-t (synth Γ tgt)]
             [_ (if (type=? tgt-t 'Nat)
                    (go 'ok)
                    (stop tgt (format "Expected Nat, got ~v" tgt-t)))]
             [_ (check Γ base tp)]
             [_ (check Γ step `(→ Nat (→ ,tp ,tp)))])
            (go tp))]
    ; Variables
    [x #:when (and (symbol? x)
                   (not (memv x '(th rec λ zero add1))))
       (match (assv x Γ)
         [#f (stop x "Variable not found")]
         [(cons _ t) (go t)])]
    ; Applications
    [`(,rator ,rand)
     (go-on ([rator-t (synth Γ rator)])
            (match rator-t
              [`(→ ,A ,B)
               (go-on ([_ (check Γ rand A)])
                      (go B))]
              [else (stop rator (format "Not a function type: ~v" rator-t))]))]))

(define (check Γ e t)
  (match e
    ['zero (if (type=? t 'Nat)
               (go 'ok)
               (stop e (format "Tried to use ~v for zero" t)))]
    [`(add1 ,n)
     (if (type=? t 'Nat)
         (go-on ([_ (check Γ n 'Nat)])
                (go 'ok))
         (stop e (format "Tried to use ~v for add1" t)))]
    [`(λ (,x) ,b)
     (match t
       [`(→ ,A ,B)
        (go-on ([_ (check (extend Γ x A) b B)])
               (go 'ok))]
       [non-arrow
        (stop e (format "Instead of → type, got ~a" non-arrow))])]
    [other
     (go-on ([t2 (synth Γ e)])
            (if (type=? t t2)
                (go 'ok)
                (stop e
                      (format "Synthesized type ~v where type ~v was expected" t2 t))))]))

(check-equal? (synth (list (cons 'x 'Nat)) 'x)
              (go 'Nat))
(check-equal? (check '() 'zero 'Nat)
              (go 'ok))
(check-equal? (check '()
                     '(λ (j)
                        (λ (k)
                          (rec Nat j k (λ (n-1)
                                         (λ (sum)
                                           (add1 sum))))))
                     '(→ Nat (→ Nat Nat)))
              (go 'ok))

(define (check-program Γ prog)
  (match prog
    ['() (go Γ)]
    [(cons `(define ,x ,e) rest)
     (go-on ([t (synth Γ e)])
            (check-program (extend Γ x t) rest))]
    [(cons e rest)
     (go-on ([t (synth Γ e)])
            (begin
              (printf "~a : ~a\n" e t)
              (check-program Γ rest)))]))

(check-program '()
               '((define three
                   (the Nat
                        (add1 (add1 (add1 zero)))))
                 (define +
                   (the (→ Nat (→ Nat Nat))
                        (λ (n)
                          (λ (k)
                            (rec Nat n
                              k
                              (λ (pred)
                                (λ (almost-sum)
                                  (add1 almost-sum))))))))
                 (+ three)
                 ((+ three) three)))

#| The Evaluator |#

;; env -> expr -> value
(define (val ρ e)
  (match e
    [`(the ,type ,expr)
     (val ρ expr)]
    ['zero (ZERO)]
    [`(add1 ,n) (ADD1 (val ρ n))]
    [x #:when (and (symbol? x)
                   (not (memv x '(the zero add1 λ rec))))
       (cdr (assv x ρ))]
    [`(λ (,x) ,b)
     (CLOS ρ x b)]
    [`(rec ,type ,target ,base ,step)
     (do-rec type (val ρ target) (val ρ base) (val ρ step))]
    [`(,rator ,rand)
     (do-ap (val ρ rator) (val ρ rand))]))

;; value -> value -> value
(define (do-ap fun arg)
  (match fun
    [(CLOS ρ x e)
     (val (extend ρ x arg) e)]
    [(NEU `(→ ,A ,B) ne)
     (NEU B (N-ap ne (THE A arg)))]))

;; type -> value -> value -> value -> value
(define (do-rec type target base step)
  (match target
    [(ZERO) base]
    [(ADD1 n)
     (do-ap (do-ap step n)
            (do-rec type n base step))]
    [(NEU 'Nat ne)
     (NEU type
          (N-rec type
                 ne
                 (THE type base)
                 (THE `(→ Nat (→ ,type ,type)) step)))]))

;; list[symbols] -> type -> value -> value
(define (read-back used-names type value)
  (match type
    ['Nat
     (match value
       [(ZERO) 'zero]
       [(ADD1 n) `(add1 ,(read-back used-names 'Nat n))]
       [(NEU _ ne)
        (read-back-neutral used-names ne)])]
    [`(→ ,A ,B)
     (let ([x (freshen used-names 'x)])
       `(λ (,x)
          ,(read-back (cons x used-names)
                      B
                      (do-ap value (NEU A (N-var x))))))]))

;; list[symbols] -> type -> value
(define (read-back-neutral used-names ne)
  (match ne
    [(N-var x) x]
    [(N-ap fun (THE arg-type arg))
     `(,(read-back-neutral used-names fun)
       ,(read-back used-names arg-type arg))]
    [(N-rec type target (THE base-type base) (THE step-type step))
     `(rec ,type
        ,(read-back-neutral used-names target)
        ,(read-back used-names base-type base)
        ,(read-back used-names step-type step))]))

#| Definitions |#

(struct def (type value) #:transparent)

(define (defs->ctx Δ)
  (match Δ
    ['() '()]
    [(cons (cons x (def type _)) rest)
     (extend (defs->ctx rest) x type)]))

(define (defs->env Δ)
  (match Δ
    ['() '()]
    [(cons (cons x (def _ value)) rest)
     (extend (defs->ctx rest) x value)]))

(define (run-program Δ prog)
  (match prog
    ['() (go Δ)]
    [(cons `(define ,x ,e) rest)
     (go-on ([type (synth (defs->ctx Δ) e)])
            (run-program (extend Δ x (def type (val (defs->env Δ) e)))
                         rest))]
    [(cons e rest)
     (let ([Γ (defs->ctx Δ)]
           [ρ (defs->env Δ)])
       (go-on ([type (synth Γ e)])
              (let ([v (val ρ e)])
                (begin
                  (printf "~a : ~a\n" type (read-back (map car Γ) type v))
                  (run-program Δ rest)))))]))

(run-program '() '((define +
                     (the (→ Nat
                             (→ Nat
                                Nat))
                          (λ (x)
                            (λ (y)
                              (rec Nat x
                                y
                                (λ (_)
                                  (λ (sum)
                                    (add1 sum))))))))
                   +
                   (+ (add1 (add1 zero)))
                   ((+ (add1 (add1 zero))) (add1 zero))))
