;; Author: Guannan Wei
;; Derived from CS352/502 lecture notes

(define (even x)
  (if (eq? x 0)
      1
      (odd (- x 1))))

(define (odd x)
  (if (eq? x 0)
      0
      (even (- x 1))))

(time (display (even 300000000)))
