#lang racket

(define-struct empty {})
(define-struct eps   {})
(define-struct char  {value})
(define-struct cat   {left right})
(define-struct alt   {this that})
(define-struct rep   {lang})

(define (δ L)
  (match L
    [(empty)  #f]
    [(eps)    #t]
    [(char _) #f]
    [(rep _)  #t]
    [(alt L1 L2) (or  (δ L1) (δ L2))]
    [(cat L1 L2) (and (δ L1) (δ L2))]))

(define (D c L)
  (match L
    [(empty) (empty)]
    [(eps)   (empty)]
    [(char a) (if (equal? c a)
                  (eps)
                  (empty))]
    [(alt L1 L2) (alt (D c L1)
                      (D c L2))]
    [(cat (and (? δ) L1) L2)
     (alt (D c L2)
          (cat (D c L1) L2))]
    [(cat L1 L2) (cat (D c L1) L2)]
    [(rep L1) (cat (D c L1) L)]))

(define (matches? w L)
  (if (null? w)
      (δ L)
      (matches? (cdr w) (D (car w) L))))

(matches? '(h e l l o) (cat (char 'h)
                            (cat (char 'e)
                                 (cat (rep (char 'l)) (char 'o)))))