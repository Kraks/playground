#lang racket
;; https://raw.githubusercontent.com/Kraks/ad/refs/heads/master/ad.rkt

(require racket/control)
(require rackunit)

#| Foward-mode |#

(struct NumF (x d)
  #:transparent)

(define NumF/cst (λ (x) (NumF x 0)))

(define (NumF/+ n1 n2)
  (NumF (+ (NumF-x n1) (NumF-x n2))
        (+ (NumF-d n1) (NumF-d n2))))

(define (NumF/* n1 n2)
  (NumF (* (NumF-x n1) (NumF-x n2))
        (+ (* (NumF-d n1) (NumF-x n2))
           (* (NumF-d n2) (NumF-x n1)))))

(define ((NumF/grad f) x) (NumF-d (f (NumF x 1))))

;; A testing example

(define df1 (NumF/grad (λ (x) (NumF/+ (NumF/* (NumF/cst 2) x)
                                      (NumF/* x (NumF/* x x))))))
(define (df-should-be n) (+ 2 (* 3 n n)))

(for ([i (range 1 10)])
  (check-equal? (df1 i) (df-should-be i)))

#| Reverse-mode |#

(struct NumR (x [d #:mutable])
  #:transparent)

(define NumR/cst (λ (x) (NumR x 0)))

(define (NumR/+ n1 n2)
  (shift k (let ([y (NumR (+ (NumR-x n1) (NumR-x n2)) 0)])
             (k y)
             (set-NumR-d! n1 (+ (NumR-d n1) (NumR-d y)))
             (set-NumR-d! n2 (+ (NumR-d n2) (NumR-d y))))))

(define (NumR/* n1 n2)
  (shift k (let ([y (NumR (* (NumR-x n1) (NumR-x n2)) 0)])
             (k y)
             (set-NumR-d! n1 (+ (NumR-d n1)
                                (* (NumR-x n2) (NumR-d y))))
             (set-NumR-d! n2 (+ (NumR-d n2)
                                (* (NumR-x n1) (NumR-d y)))))))

(define ((NumR/grad f) x)
  (let ([z (NumR x 0)])
    (reset (set-NumR-d! (f z) 1))
    (NumR-d z)))

(define df2 (NumR/grad (λ (x) (NumR/+ (NumR/* (NumR/cst 2) x)
                                      (NumR/* x (NumR/* x x))))))

(for ([i (range 1 10)])
  (check-equal? (df2 i) (df-should-be i)))
