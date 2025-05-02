#lang racket

;; Untyped NbE

(require rackunit)
(require "error.rkt")

(struct CLOS (env var body)
  #:transparent)

(define (extend ρ x v)
  (cons (cons x v) ρ))

#| Generating Fresh Names |#

(define (add-* x)
  (string->symbol (string-append (symbol->string x) "*")))

(define (freshen used x)
  (if (memv x used)
      (freshen used (add-* x))
      x))

(check-eq? (freshen '() 'x) 'x)
(check-eq? (freshen '(x x*) 'x) 'x**)
(check-eq? (freshen '(x y z) 'y) 'y*)

#| Normalizing Untyped λ-Calculus |#

#|
Normal forms:

<norm> ::= <neu>
         | ( λ ( <id> ) <norm> )
<neu>  ::= <id>
         | ( <neu> <norm> )
|#

;; neutral variable
(struct N-var (name))

;; neutral application
(struct N-ap (rator rand))

(define (val ρ e)
  (match e
    [`(λ (,x) ,b) (CLOS ρ x b)]
    [x #:when (symbol? x)
       (let ([xv (assv x ρ)])
         (if xv
             (cdr xv)
             (error 'val "Unknown variable ~v" x)))]
    [`(,rator ,rand)
     (do-ap (val ρ rator) (val ρ rand))]))

(define (do-ap fun arg)
  (match fun
    [(CLOS ρ x b)
     (val (extend ρ x arg) b)]
    ; If the argument is neutral, construct a bigger neutral expression.
    [neutral-fun
     (N-ap fun arg)]))

(define (read-back used-names v)
  (match v
    [(CLOS ρ x body)
     (let* ([y (freshen used-names x)]
            [neutral-y (N-var y)])
       `(λ (,y) ,(read-back (cons y used-names)
                            (val (extend ρ x neutral-y) body))))]
    [(N-var x) x]
    [(N-ap rator rand)
     `(,(read-back used-names rator) ,(read-back used-names rand))]))

(check-equal?
 (read-back '() (val '() '((λ (x) (λ (y) (x y)))
                           (λ (z) z))))
 '(λ (y) y))

(define (norm ρ e)
  (read-back '() (val ρ e)))

(define (run-program ρ exprs)
  (match exprs
    [(list) (void)]
    [(list `(define ,x ,e) rest ...)
     (let ([v (val ρ e)])
       (run-program (extend ρ x v) rest))]
    [(list e rest ...)
     (displayln (norm ρ e))
     (run-program ρ rest)]))

#| Church Numerals |#

(define (with-numerals e)
  `((define church-zero
      (λ (f) (λ (x) x)))
    (define church-add1
      (λ (n-1) (λ (f) (λ (x) (f ((n-1 f) x))))))
    ,e))

(define (to-church n)
  (cond [(zero? n) 'church-zero]
        [(positive? n)
         (let ([church-of-n-1 (to-church (sub1 n))])
           `(church-add1 ,church-of-n-1))]))

(run-program '() (with-numerals (to-church 0))) ;; (λ (f) (λ (x) x))

(run-program '() (with-numerals (to-church 5))) ;; (λ (f) (λ (x) (f (f (f (f (f x)))))))

(define church-add
  '(λ (j)
     (λ (k)
       (λ (f)
         (λ (x)
           ((j f) ((k f) x)))))))

(define church-mult
  '(λ (j)
     (λ (k)
       (λ (f)
         (λ (x)
           ((j (k f)) x))))))

(run-program '()
             (with-numerals `((,church-add ,(to-church 2))
                              ,(to-church 2))))

(run-program '()
             (with-numerals `((,church-mult ,(to-church 2))
                              ,(to-church 3))))

