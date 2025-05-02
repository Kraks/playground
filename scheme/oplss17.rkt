#lang racket

;; 6/30 Sam

;; argmax : [A -> Number] [Listof A] -> A
;; the returned value must max the function
;; the list must not be empty
;; the returned value must be in the list
;; the numbers must be comparable
;; pick the first when two numbers are the same
;; the function should be total on the input
;; the function should not be called twice on any element
;; the function must not change the file system

(module sam6/30 typed/racket
  (define-type (Non-Empty-Listof A)
    (Pair A (Listof A)))
  
  (provide argmax)
  
  (: argmax : (All (A) [A -> Real] [Non-Empty-Listof A] -> A))
  (define (argmax f l)
    (let loop ([fv (f (first l))]
               [v (first l)]
               [l (rest l)])
      (cond [(empty? l) v]
            [(> (f (first l)) fv)
             (loop (f (first l)) (first l) (rest l))]
            [else
             (loop fv v (rest l))])))

  (argmax (λ (x) 3.2) (list 1 2 3))
  )

;; even if we have contract, is there still runtime type checking inside of function

(provide (contract-out
          [my-argmax (->i ([f (-> any/c real?)]
                           [l (and/c list? pair?)])
                           [res (l) (λ  (r) (member r l))])]))
(define (my-argmax f l)
    (let loop ([fv (f (first l))]
               [v (first l)]
               [l (rest l)])
      (cond [(empty? l) v]
            [(> (f (first l)) fv)
             (loop (f (first l)) (first l) (rest l))]
            [else
             (loop fv v (rest l))])))

(my-argmax (λ (x) x) (list 1 2 3))
