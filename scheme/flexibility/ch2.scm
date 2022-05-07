(define (compose f g)
  (lambda args
    (f (apply g args))))

(define (identity x) x)

(define (iterate n f)
  (if (= n 0)
      identity
      (compose f (iterate (- n 1) f))))

(define (square x) (* x x))

;; analogy: function composition is like multiplication,
;; and function iteration is like exponentiation.

((iterate 3 square) 5)

(define (parallel-combine h f g)
  (define (the-combination . args)
    (h (apply f args) (apply g args)))
  the-combination)

((parallel-combine list
                   (lambda (x y z) (list 'foo x y z))
                   (lambda (u v w) (list 'bar u v w)))
 'a 'b 'c)
