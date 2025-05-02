#lang racket

(require racket/contract)

(define greater-than-nine?
  (λ (x) (> x 9)))

(define between-zero-and-ninety-nine?
  (λ (x) (and (>= x 0) (<= x 99))))

(define/contract g
  (-> (-> greater-than-nine? between-zero-and-ninety-nine?) between-zero-and-ninety-nine?)
  (λ (f) (f 10)))

;(g (λ (x) x))

(g (λ (x) (- 0 x)))