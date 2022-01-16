#lang racket

(provide stringify)

;; shallow embedding

(define p1
  (λ (x) ((λ (y) y) x)))

(displayln (p1 7))

;; deep embedding

(define p2
  '(fun x (app (fun y y) x)))

(displayln p2)

;; HOAS

(define n-vars 0)
(define (fresh)
  (define n (+ n-vars 1))
  (set! n-vars n)
  (string->symbol (string-append "x" (number->string n))))

(define (struct e)
  (match e
    [(? list?) (map struct e)]
    [(? procedure?)
     (define x (fresh))
     `(,x ,(struct (e x)))]
    [else e]))

(define (stringify e)
  (define n n-vars)
  (define r (struct e))
  (set! n-vars n)
  r)

(define p3
  (list 'fun (λ (x) (list 'app (list 'fun (λ (y) y)) x))))
(displayln (stringify p3))

;; Tagless-final with NbE

(define (fun f) (list 'fun f))
(define (app f a)
  (if (and (list? f) (equal? (first f) 'fun))
      ((second f) a)
      (list 'app f a)))
(define p4
  (fun (λ (x) (app (fun (λ (y) y)) x))))
(displayln (stringify p4))