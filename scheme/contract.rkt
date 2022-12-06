#lang racket

(require racket/contract)

(define greater-than-nine?
  (λ (x) (> x 9)))

(define between-zero-and-ninety-nine?
  (λ (x) (and (>= x 0) (<= x 99))))

(define/contract g1
  (-> (-> greater-than-nine? between-zero-and-ninety-nine?) between-zero-and-ninety-nine?)
  (λ (f) (f 0)))

(define/contract g2
  (-> (-> greater-than-nine? between-zero-and-ninety-nine?) between-zero-and-ninety-nine?)
  (λ (f) (f 10)))

;(g1 (λ (x) x))

;(g (λ (x) (- 0 x)))

;(g2 (λ (x) (- 0 x)))

(define (blame s) (error 'contract "~a" s))

(define (immediate pred?)
  (λ (val)
    (if (pred? val) val (blame val))))

(define d/dx
  (λ (f)
    (λ (x)
      (/ (- (f (+ x 0.001))
            (f x))
         0.001))))

(define (guard ctc val) (ctc val))

(define (function dom rng)
  (λ (f)
    (if (procedure? f)
        (λ (x) (rng (f (dom x))))
        (blame f))))

(define con-d/dx (guard (function (immediate number?)
                                  (immediate number?))
                        d/dx))

((con-d/dx (λ (x) (+ x 1))) 3)
