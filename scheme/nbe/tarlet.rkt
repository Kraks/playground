#lang racket

(define keywords
  (list 'define
        'U
        'Nat 'zero 'add1 'ind-Nat
        'Σ 'Sigma 'λ 'lambda
        '= 'same  'replace
        'Trivial  'sole
        'Absurd 'ind-Absurd
        'Atom 'quote
        'the))

(define (keyword? x)
  (if (memv x keywords)
      #t
      #f))

(define (var? x)
  (and (symbol? x)
       (not (keyword? x))))

#| α-equivalence |#

(define (α-equiv? e1 e2)
  (α-equiv-aux e1 e2 '() '()))

