#lang racket

(require racket/control)

(define (flip)
  (shift k (begin (k #t) (k #f) (fail))))

(define (fail)
  (shift k "no"))

(define (choice n)
  (if (< n 1)
      (fail)
      (if (flip) (choice (- n 1)) n)))

(define (triple n s)
  (let* ([i (choice n)]
         [j (choice (- i 1))]
         [k (choice (- j 1))])
    (if (= (+ i j k) s)
        (list i j k)
        (fail))))

(triple 9 15)
