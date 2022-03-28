#lang racket

(require racket/control)

#|
Section 1.7
The two programs demonstrate the difference between control/prompt and shift/reset.
|#

(define (reverse xs)
  (define (visit xs)
    (match xs
      [(list) (list)]
      [(cons x xs)
       (visit (control k (cons x (k xs))))]))
  (prompt (visit xs)))

(reverse (list 1 2 3))

(define (same xs)
  (define (visit xs)
    (match xs
      [(list) (list)]
      [(cons x xs)
       (visit (shift k (cons x (k xs))))]))
  (reset (visit xs)))

(same (list 1 2 3))

;; Using prompt/control to simulate shift/reset

(define (same1 xs)
  (define (visit xs)
    (match xs
      [(list) (list)]
      [(cons x xs)
       (visit (control k (cons x (prompt (k xs)))))]))
  (prompt (visit xs)))

(same1 (list 1 2 3))

;; TODO: using shift/reset to simulate prompt/control