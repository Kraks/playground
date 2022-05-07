#lang racket

#|
Code from David Christiansen's tutorial:
  http://davidchristiansen.dk/tutorials/nbe
|#

(require rackunit)

#| Values and Runtime Environments |#

(struct CLOS (env var body)
  #:transparent)

(define (extend ρ x v)
  (cons (cons x v) ρ))

(define (val ρ e)
  (match e
    [`(λ (,x) ,b) (CLOS ρ x b)]
    [x #:when (symbol? x)
     (let ([xv (assv x ρ)])
       (if xv (cdr xv)
           (error 'val "unknown variable ~a" x)))]
    [`(,rator ,rand)
     (do-ap (val ρ rator) (val ρ rand))]))

(define (do-ap clos arg)
  (match clos
    [(CLOS ρ x b)
     (val (extend ρ x arg) b)]))

(check-equal? (val '() '(λ (x) (λ (y) y)))
              (CLOS '() 'x '(λ (y) y)))
(check-equal? (val '() '((λ (x) x) (λ (x) x)))
              (CLOS '() 'x 'x))
(check-exn exn:fail? (λ () (val '() 'x)))

(define (run-prog ρ exprs)
  (match exprs
    ['() (void)]
    [(cons `(define ,x ,e) rest)
     (let ([v (val ρ e)])
       (run-prog (extend ρ x v) rest))]
    [(cons e rest)
     (displayln (val ρ e))
     (run-prog ρ rest)]))

(check-equal?
 (run-prog '() '((define id (λ (x) x))
                 (id (λ (y) (λ (z) (z y))))))
 (void))