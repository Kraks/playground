#lang gamble

(require gamble/viz)

(flip)

(repeat (lambda () (flip 0.3)) 10)

(define s-or2flips
  (rejection-sampler
   (define A (flip))
   (define B (flip))
   (or A B)))

(s-or2flips)

(define s-or
    (rejection-sampler
      (define A (flip))
      (define B (flip))
      (observe/fail (or A B))
      A))

(hist (repeat s-or 100))