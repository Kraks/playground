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

(module simple-contract racket

  (define (blame s) (error 'contract "~a" s))

  (define (immediate pred?)
    (λ (val)
      (if (pred? val) val (blame val))))

  (define (guard ctc val) (ctc val))

  (define (mk-fun-contract dom rng)
    (λ (f)
      (if (procedure? f)
          (λ (x) (rng (f (dom x))))
          (blame f))))

  (define d/dx
    (λ (f)
      (λ (x)
        (/ (- (f (+ x 0.001))
              (f x))
           0.001))))

  (define con-d/dx
    (guard (mk-fun-contract
            (mk-fun-contract (immediate number?)
                             (immediate number?))
            (mk-fun-contract (immediate number?)
                             (immediate number?)))
           d/dx))

  ((con-d/dx (λ (x) (+ x 1))) 3)

  )

(require 'simple-contract)

;; with blame

(define (guard ctc val pos neg)
  ((ctc pos neg) val))

(define (blame s) (error 'contract "~a" s))

(define (immediate pred?)
  (λ (pos neg)
    (λ (val)
      (if (pred? val) val (blame pos)))))

(define (function dom rng)
  (λ (pos neg)
    (let ([doc-c (dom neg pos)]
          [rng-c (rng pos neg)])
      (λ (val)
        (if (procedure? val)
            (λ (x) (rng-c (val (doc-c x))))
            (blame pos))))))
