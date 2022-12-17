#lang racket

(require rackunit)

#| Negation Normal Form |#

;; TODO: Add biconnection for NNF transformation

(define (nnf prop)
  (match prop
    ['(¬ ⊤) '⊥]
    ['(¬ ⊥) '⊤]
    [(? symbol? x) x]
    [`(¬ ,(? symbol? x)) `(¬ ,x)]
    [`(¬ (¬ ,p)) (nnf p)]
    [`(¬ (,p → ,q)) (nnf `(¬ ((¬ ,p) ∨ ,q)))]
    [`(¬ (,p ∧ ,q)) (nnf `((¬ ,p) ∨ (¬ ,q)))]
    [`(¬ (,p ∨ ,q)) (nnf `((¬ ,p) ∧ (¬ ,q)))]
    [`(,p → ,q) (nnf `((¬ ,p) ∨ ,q))]
    [`(,p ∧ ,q) `(,(nnf p) ∧ ,(nnf q))]
    [`(,p ∨ ,q) `(,(nnf p) ∨ ,(nnf q))]))

(module+ test
  (check-eq? (nnf 'x)
             'x)
  
  (check-equal? (nnf '(¬ a))
                '(¬ a))
  
  (check-eq? (nnf '(¬ (¬ a)))
             'a)
  
  (check-equal? (nnf '(a ∧ b))
                '(a ∧ b))
  
  (check-equal? (nnf '(a ∨ b))
                '(a ∨ b))
  
  (check-equal? (nnf '(¬ (a ∧ b)))
                '((¬ a) ∨ (¬ b)))
  
  (check-equal? (nnf '((¬ (a ∧ (¬ b))) ∧ c))
                '(((¬ a) ∨ b) ∧ c))

  (check-equal? (nnf '(¬ ((a ∧ b) ∧ b)))
                '(((¬ a) ∨ (¬ b)) ∨ (¬ b)))

  (check-equal? (nnf '(¬ (p → (¬ (p ∧ q)))))
                '(p ∧ (p ∧ q)))

  (check-equal? (nnf '(p → q))
                '((¬ p) ∨ q))

  (check-equal? (nnf '(¬ ((¬ (p ∧ q)) → (¬ r))))
                '(((¬ p) ∨ (¬ q)) ∧ r))
  )

#| Disjunctive Normal Form |#

(define (dnf/dist prop)
  (match prop
    [`((,p ∨ ,q) ∧ ,r) `(,(dnf/dist `(,p ∧ ,r)) ∨ ,(dnf/dist `(,q ∧ ,r)))]
    [`(,p ∧ (,q ∨ ,r)) `(,(dnf/dist `(,p ∧ ,q)) ∨ ,(dnf/dist `(,p ∧ ,r)))]
    [p p]))

(define dnf (compose dnf/dist nnf))

(module+ test
  (check-equal? (dnf/dist '((p ∨ q) ∧ r))
                '((p ∧ r) ∨ (q ∧ r)))

  (check-equal? (dnf/dist '(p ∧ (q ∨ r)))
                '((p ∧ q) ∨ (p ∧ r)))

  (check-equal? (dnf '((Q1 ∨ (¬ (¬ Q2))) ∧ ((¬ R1) → R2)))
                '(((Q1 ∧ R1) ∨ (Q1 ∧ R2)) ∨ ((Q2 ∧ R1) ∨ (Q2 ∧ R2))))
  )

#| Conjunctive Normal Form |#

(define (cnf/dist prop)
  (match prop
    [`((,p ∧ ,q) ∨ ,r) `(,(cnf/dist `(,p ∨ ,r)) ∧ ,(cnf/dist `(,q ∨ ,r)))]
    [`(,p ∨ (,q ∧ ,r)) `(,(cnf/dist `(,p ∨ ,q)) ∧ ,(cnf/dist `(,p ∨ ,r)))]
    [p p]))

(define cnf (compose cnf/dist nnf))

(module+ test
  (check-equal? (cnf '((Q1 ∧ (¬ (¬ Q2))) ∨ ((¬ R1) → R2)))
                '((Q1 ∨ (R1 ∨ R2)) ∧ (Q2 ∨ (R1 ∨ R2))))
  )

#| Validity by Semantic Augment Method |#

(struct ⊨ (formula) #:transparent)
(struct ⊭ (formula) #:transparent)
(struct And (fs) #:transparent)
(struct Or (fs) #:transparent)
(struct None () #:transparent)

(define (deduce asmp)
  (match asmp
    [(⊨ `(¬ ,p)) (And (list (⊭ p)))]
    [(⊭ `(¬ ,p)) (And (list (⊨ p)))]
    [(⊨ `(,p ∧ ,q)) (And (list (⊨ p) (⊨ q)))]
    [(⊭ `(,p ∧ ,q)) (Or (list (⊭ p) (⊭ q)))]
    [(⊨ `(,p ∨ ,q)) (Or (list (⊨ p) (⊨ q)))]
    [(⊭ `(,p ∨ ,q)) (And (list (⊭ p) (⊭ q)))]
    [(⊨ `(,p → ,q)) (Or (list (⊭ p) (⊨ q)))]
    [(⊭ `(,p → ,q)) (And (list (⊨ p) (⊭ q)))]
    [(⊨ `(,p ↔ ,q)) (Or (list (⊨ `(,p ∧ ,q)) (⊭ `(,p ∨ ,q))))]
    [(⊭ `(,p ↔ ,q)) (Or (list (⊨ `(,p ∧ (¬ ,q))) (⊨ `((¬ ,p) ∧ ,q))))]
    [p (None)]))

(define (contradict? p asmps)
  (match asmps
    [(list) #f]
    [(list q rest ...)
     (match* (p q)
       [((⊨ f) (⊭ f)) #t]
       [((⊭ f) (⊨ f)) #t]
       [(_ _) (contradict? p rest)])]))

(define (contradict*? ps asmps)
  (foldl (λ (p b) (or b (contradict? p asmps))) #f ps))

(define (valid? p)
  (define asmp (⊭ p))
  (define (valid/aux? worklist asmps)
    ;(displayln worklist)
    (match worklist
      [(list) #f]
      [(list q rest ...)
       (if (contradict? q asmps) #t
           (match (deduce q)
             [(And fs) (valid/aux? (append fs rest) (append fs asmps))]
             [(Or fs) (foldl (λ (f b) (and b (valid/aux? (cons f rest) (cons f asmps)))) #t fs)]
             [(None) (valid/aux? rest asmps)]))]))
  (valid/aux? (list asmp) (list asmp)))

(module+ test
  (check-equal? (deduce (⊭ '((P ∧ Q) → (P ∨ (¬ Q)))))
                (And (list (⊨ '(P ∧ Q)) (⊭ '(P ∨ (¬ Q))))))
  
  (check-equal? (deduce (⊨ '(P ∧ Q)))
                (And (list (⊨ 'P) (⊨ 'Q))))
  
  (check-equal? (deduce (⊭ '(P ∨ (¬ Q))))
                (And (list (⊭ 'P) (⊭ '(¬ Q)))))
  
  (check-equal? (deduce (⊭ '(¬ Q)))
                (And (list (⊨ 'Q))))
  
  (check-equal? (deduce (⊨ '(P ∨ Q)))
                (Or (list (⊨ 'P) (⊨ 'Q))))

  (check-false (contradict? (⊨ 'a) (list (⊨ 'b) (⊭ 'c))))
  
  (check-false (contradict? (⊨ 'a) (list (⊨ 'a) (⊨ 'b) (⊭ 'd))))
  
  (check-true (contradict? (⊨ '(p ∨ q)) (list (⊨ 'b) (⊭ '(p ∨ q)))))
  
  (check-true (contradict? (⊭ '(a ∧ (¬ b))) (list (⊨ 'q) (⊭ 'c) (⊨ '(a ∧ (¬ b))))))
  
  (check-true (valid? '((P ∧ Q) →  (P ∨ (¬ Q)))))
  
  (check-true (valid? '(((P → Q) ∧ (Q → R)) → (P → R))))
  
  (check-false (valid? '(P ∧ Q)))
  
  (check-false (valid? '(P ∨ Q)))
  
  (check-true (valid? '(A ∨ (¬ A))))

  (check-false (valid? '(((P → Q) ∨ P) ∧ (¬ Q))))

  (check-true (valid? '((P → Q) ∨ (P ∧ (¬ Q)))))

  (check-true (valid? '((A → B) ↔ ((¬ B) → (¬ A)))))

  (check-true (valid? '((((¬ A) → B) ∧ ((¬ A) → (¬ B))) → A)))

  (check-true (valid? '((¬ (A ∧ B)) ↔ ((¬ A) ∨ (¬ B)))))

  (check-true (valid? '(C → C)))

  (check-true (valid? '((A ∨ B) → (A ∨ B))))

  (check-false (valid? '((P → (Q → R)) → ((¬ R) → ((¬ Q) → (¬ P))))))
  )

#| Tseitin's Transformation |#

(define (subformulae f)
  (set-union
   (set f)
   (match f
     [(? symbol? x) (set)]
     [`(¬ ,x) (set-union (subformulae x))]
     [`(,p ∧ ,q) (set-union (subformulae p) (subformulae q))]
     [`(,p ∨ ,q) (set-union (subformulae p) (subformulae q))]
     [`(,p → ,q) (set-union (subformulae p) (subformulae q))]
     [`(,p ↔ ,q) (set-union (subformulae p) (subformulae q))])))

(define (formula->string f)
  (match f
    [(? symbol? x) (symbol->string x)]
    [`(¬ ,x) (string-append "¬" (formula->string x))]
    [`(,p ∧ ,q) (string-append "<" (formula->string p) " ∧ " (formula->string q) ">")]
    [`(,p ∨ ,q) (string-append "<" (formula->string p) " ∨ " (formula->string q) ">")]
    [`(,p → ,q) (string-append "<" (formula->string p) " → " (formula->string q) ">")]
    [`(,p ↔ ,q) (string-append "<" (formula->string p) " ↔ " (formula->string q) ">")]))

(define (rep f)
  (match f
    ['⊤ '⊤] ['⊥ '⊥]
    [(? symbol? x) x]
    [else (string->symbol (string-append "ϕ" (formula->string f)))]))

(define (encode f)
  (define p (rep f))
  (match f
    ['⊤ '⊤] ['⊥ '⊥]
    [(? symbol? x) '⊤]
    [`(¬ ,f) `(((¬ ,p) ∨ (¬ ,(rep f))) ∧ (,p ∨ ,(rep f)))]
    [`(,f1 ∧ ,f2)
     `(((¬ ,p) ∨ ,(rep f1)) ∧
       ((¬ ,p) ∨ ,(rep f2)) ∧
       ((¬ ,(rep f1)) ∨ (¬ ,(rep f2)) ∨ ,p))]
    [`(,f1 ∨ ,f2)
     `(((¬ ,p) ∨ ,(rep f1) ∨ ,(rep f2)) ∧
       ((¬ ,(rep f1)) ∨ ,p) ∧
       ((¬ ,(rep f2)) ∨ ,p))]
    [`(,f1 → ,f2)
     `(((¬ ,p) ∨ (¬ ,(rep f1)) ∨ ,(rep f2)) ∧
       (,(rep f1) ∨ ,p) ∧
       ((¬ ,(rep f2)) ∨ ,p))]
    [`(,f1 ↔ ,f2)
     `(((¬ ,p) ∨ (¬ ,(rep f1)) ∨ ,(rep f2)) ∧
       ((¬ ,p) ∨ ,(rep f1) ∨ (¬ ,(rep f2))) ∧
       (,p ∨ (¬ ,(rep f1)) ∨ (¬ ,(rep f2))) ∧
       (,p ∨ ,(rep f1) ∨ ,(rep f2)))]))

(define (all-but-last lst) (reverse (rest (reverse lst))))

(define (cnf/simplify f)
  (match f
    [`(,p ∧ ⊤) `(,p)]
    [`(⊤ ∧ ,rest ...) (cnf/simplify rest)]
    [`(,p ∧ ,rest ...) `(,p ∧ ,@(cnf/simplify rest))]
    [else f]))

(define (tseitin f)
  (define ensf (map encode (set->list (subformulae f))))
  (define conj/ensf (foldr (λ (f all)
                             (if (list? f) `(,@f ∧ ,@all) `(,f ∧ ,@all)))
                           (last ensf) (all-but-last ensf)))
  (cnf/simplify `(,(rep f) ∧ ,@conj/ensf)))

(module+ test
  (check-equal? (subformulae '((Q1 ∧ Q2) ∨ (R1 ∧ R2)))
                (set 'R1 'R2 'Q1 'Q2
                     '(R1 ∧ R2) '(Q1 ∧ Q2)
                     '((Q1 ∧ Q2) ∨ (R1 ∧ R2))))
  (check-equal? (subformulae '(¬ ((¬ (p ∧ q)) → (¬ r))))
                (set
                 '(¬ r)
                 '(¬ (p ∧ q))
                 '((¬ (p ∧ q)) → (¬ r))
                 '(p ∧ q)
                 '(¬ ((¬ (p ∧ q)) → (¬ r)))
                 'r
                 'q
                 'p))

  (check-equal? (formula->string '(((¬ Q1) ∧ Q2) ∨ (R1 ∧ (¬ R2))))
                "<<¬Q1 ∧ Q2> ∨ <R1 ∧ ¬R2>>")
  
  (check-equal? (cnf/simplify '(a ∧ b))
                '(a ∧ b))
  (check-equal? (cnf/simplify '(a ∧ ⊤ ∧ b ∧ ⊤))
                '(a ∧ b))
  (check-equal? (cnf/simplify '(a ∧ b ∧ c ∧ d ∧ ⊤))
                '(a ∧ b ∧ c ∧ d))
  
  (check-equal? (tseitin '((Q1 ∧ Q2) ∨ (R1 ∧ R2)))
                '(|ϕ<<Q1 ∧ Q2> ∨ <R1 ∧ R2>>|
                  ∧
                  ((¬ |ϕ<R1 ∧ R2>|) ∨ R1)
                  ∧
                  ((¬ |ϕ<R1 ∧ R2>|) ∨ R2)
                  ∧
                  ((¬ R1) ∨ (¬ R2) ∨ |ϕ<R1 ∧ R2>|)
                  ∧
                  ((¬ |ϕ<<Q1 ∧ Q2> ∨ <R1 ∧ R2>>|) ∨ |ϕ<Q1 ∧ Q2>| ∨ |ϕ<R1 ∧ R2>|)
                  ∧
                  ((¬ |ϕ<Q1 ∧ Q2>|) ∨ |ϕ<<Q1 ∧ Q2> ∨ <R1 ∧ R2>>|)
                  ∧
                  ((¬ |ϕ<R1 ∧ R2>|) ∨ |ϕ<<Q1 ∧ Q2> ∨ <R1 ∧ R2>>|)
                  ∧
                  ((¬ |ϕ<Q1 ∧ Q2>|) ∨ Q1)
                  ∧
                  ((¬ |ϕ<Q1 ∧ Q2>|) ∨ Q2)
                  ∧
                  ((¬ Q1) ∨ (¬ Q2) ∨ |ϕ<Q1 ∧ Q2>|)))

  (check-equal? (subformulae '(¬ ((¬ (p ∧ q)) → (¬ r))))
                (set '(¬ r) '(¬ (p ∧ q)) '((¬ (p ∧ q)) → (¬ r))
                     '(p ∧ q) '(¬ ((¬ (p ∧ q)) → (¬ r))) 'r 'q 'p))

  (check-equal? (tseitin '(¬ ((¬ (p ∧ q)) → (¬ r))))
                '(|ϕ¬<¬<p ∧ q> → ¬r>|
                  ∧
                  ((¬ |ϕ¬<¬<p ∧ q> → ¬r>|) ∨ (¬ |ϕ<¬<p ∧ q> → ¬r>|))
                  ∧
                  (|ϕ¬<¬<p ∧ q> → ¬r>| ∨ |ϕ<¬<p ∧ q> → ¬r>|)
                  ∧
                  ((¬ |ϕ<p ∧ q>|) ∨ p)
                  ∧
                  ((¬ |ϕ<p ∧ q>|) ∨ q)
                  ∧
                  ((¬ p) ∨ (¬ q) ∨ |ϕ<p ∧ q>|)
                  ∧
                  ((¬ |ϕ<¬<p ∧ q> → ¬r>|) ∨ (¬ |ϕ¬<p ∧ q>|) ∨ ϕ¬r)
                  ∧
                  (|ϕ¬<p ∧ q>| ∨ |ϕ<¬<p ∧ q> → ¬r>|)
                  ∧
                  ((¬ ϕ¬r) ∨ |ϕ<¬<p ∧ q> → ¬r>|)
                  ∧
                  ((¬ |ϕ¬<p ∧ q>|) ∨ (¬ |ϕ<p ∧ q>|))
                  ∧
                  (|ϕ¬<p ∧ q>| ∨ |ϕ<p ∧ q>|)
                  ∧
                  ((¬ ϕ¬r) ∨ (¬ r))
                  ∧
                  (ϕ¬r ∨ r)))
  ; (tseitin '(¬ ((¬ (p ∧ q)) → (¬ r))))
  )