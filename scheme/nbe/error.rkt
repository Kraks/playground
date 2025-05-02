#lang racket

(require (for-syntax syntax/parse))

(provide go stop go-on)

#| Error handling |#

(struct go (result) #:transparent)

(struct stop (expr message) #:transparent)

(define-syntax (go-on stx)
  (syntax-parse stx
    [(go-on () result)
     (syntax/loc stx result)]
    [(go-on ([pat0 e0] [pat e] ...) result)
     (syntax/loc stx
       (match e0
         [(go pat0) (go-on ([pat e] ...) result)]
         [(go v) (error 'go-on "Pattern did not match value ~v" v)]
         [(stop expr msg) (stop expr msg)]))]))

(define (bigger-than-two n)
  (if (> n 2)
      (go n)
      (stop n "Not greater than two")))

(go-on ([x (bigger-than-two 4)]
        [y (bigger-than-two 5)])
       (go (+ x y)))

(go-on ([x (bigger-than-two 1)]
          [y (bigger-than-two 5)])
    (go (+ x y)))