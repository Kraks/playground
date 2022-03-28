#lang racket

(define (sqr x) (* x x))
(define (mul x y) (* x y))

;; Section 5.2.2 Two-level programming in Scheme

;; An ordinary power implementation
(define power
  (lambda (x n)
    (letrec ([visit (lambda (n)
                      (if (zero? n) 1
                          (visit-positive n)))]
             [visit-positive (lambda (m)
                               (if (even? m)
                                   (sqr (visit-positive (quotient m 2)))
                                   (mul (sqr (visit (quotient m 2))) x)))])
      (visit n))))

;; A two-level implementation
;; n : a first-level number
;; x : a second-level number
(define powergen
  (lambda (n)
    `(lambda (x)
       ,(letrec ([visit (lambda (n)
                          (if (zero? n) '1
                              (visit-positive n)))]
                 [visit-positive (lambda (m)
                                   (if (even? m)
                                       `(sqr ,(visit-positive (quotient m 2)))
                                       `(mul (sqr ,(visit (quotient m 2))) x)))])
          (visit n)))))

(define a-power-app `(,(powergen 10) 2))
(define-namespace-anchor arith)
(eval a-power-app (namespace-anchor->namespace arith))

;; Reflection: given the name of a unary function, reflect1 yeilds a unary function that,
;; given the representation of an argument, yields the representation of a call of the
;; named function to this argument.

(define reflect1
  (lambda (f)
    (lambda (x)
      `(,f ,x))))

(define reflect2
  (lambda (f)
    (lambda (x y)
      `(,f ,x ,y))))

;; Reification: Given a polymorphic unary function, reify1 yields a representation of
;; this function.

(define reify1
  (lambda (f)
    `(lambda (x) ,(f 'x))))

(set! sqr (reflect1 'sqr))
(set! mul (reflect2 'mul))

(define power_x ;; int -> exp
  (lambda (n)
    (reify1 (lambda (x) (power x n)))))

;; Section 5.2.5 Type-directed partial evaluation

(module 5-2-5 racket
  (provide residualize)

  (struct Base (name) #:transparent)
  (struct Prod (fst-ty snd-ty) #:transparent)
  (struct Func (dom-ty rge-ty) #:transparent)

  (define parse-type
    (lambda (t)
      (match t
        [(? symbol? t) (Base t)]
        [`(,a * ,b) (Prod (parse-type a) (parse-type b))]
        [`(,a -> ,b) (Func (parse-type a) (parse-type b))]
        [`(,a -> ,b ...) (Func (parse-type a) (parse-type b))])))

  ;; type-directed map from values to representations
  (define reify
    (lambda (t v)
      (match t
        [(Base _) v]
        [(Prod t1 t2)
         `(cons ,(reify t1 (car v))
                ,(reify t2 (cdr v)))]
        [(Func t1 t2)
         (let ([x1 (gensym 'x)])
           `(lambda (,x1)
              ,(reify t2 (v (reflect t1 x1)))))])))

  ;; type-directed map from representations to values
  (define reflect
    (lambda (t e)
      (match t
        [(Base _) e]
        [(Prod t1 t2)
         (cons (reflect t1 `(car ,e))
               (reflect t2 `(cdr ,e)))]
        [(Func t1 t2)
         (lambda (v1)
           (reflect t2 `(,e ,(reify t1 v1))))])))

  ;; two-level η-expansion
  (define residualize
    (lambda (v t)
        (reify (parse-type t) v)))

  (define make-power
    ;; int -> (a -> a) * (a * a -> a) -> a -> a
    (lambda (n)
      (lambda (sqr mul)
        (lambda (x)
          (letrec ([visit (lambda (n)
                            (if (zero? n) 1
                                (visit-positive n)))]
                   [visit-positive (lambda (m)
                                     (if (even? m)
                                         (sqr (visit-positive (quotient m 2)))
                                         (mul (sqr (visit (quotient m 2))) x)))])
            (visit n))))))

  (define power
    (lambda (x n)
      (((make-power n)
        (lambda (i) (* i i))
        (lambda (x y) (* x y)))
       x)))

  (residualize
   ((make-power 10) (lambda (i) `(sqr ,i)) (lambda (x y) `(mul ,x ,y)))
   '(int -> int))

  )

(require '5-2-5)

(residualize (lambda (x) (power x 10)) '(a -> a))
;; (lambda (x15632) (sqr (mul (sqr (sqr (mul (sqr 1) x15632))) x15632)))

;; Section 5.2.6

;; Note: the residualize is normal order reduction
;; E.g., the following will produce
(residualize (lambda (f)
               (lambda (x)
                 (car (cons 42 (f x)))))
             '((a -> b) -> a -> int))

(residualize (lambda (add)
               (lambda (f)
                 (lambda (x)
                   ((lambda (y) ((add y) y)) (f x)))))
             '((a -> a -> a) -> (a -> a) -> a -> a))
;; will produce
#|
(lambda (add) (lambda (f) (lambda (x)
  ((add (f x)) (f x)))))
|#

;; Section 5.2.7 Type-directed partial evaluation with let insertion

(module 5-2-7 racket
  (require racket/control)

  (provide residualize)
  (provide make-power)
  
  (struct Base (name) #:transparent)
  (struct Prod (ty1 ty2) #:transparent)
  (struct Func (ty1 ty2) #:transparent)
  (struct Proc (ty1 ty2) #:transparent) ;; functions with effects

  (define count 1)
  (define (fresh-name x)
    (let ([c count])
      (begin
        (set! count (+ 1 count))
        (string->symbol
         (string-append (symbol->string x) (number->string c))))))

  (define parse-type
    (lambda (t)
      (match t
        [(? symbol? t) (Base t)]
        [`(,a * ,b) (Prod (parse-type a) (parse-type b))]
        [`(,a -> ,b) (Func (parse-type a) (parse-type b))]
        [`(,a -!> ,b) (Proc (parse-type a) (parse-type b))]
        [`(,a -> ,b ...) (Func (parse-type a) (parse-type b))]
        [`(,a -!> ,b ...) (Proc (parse-type a) (parse-type b))])))

  (define reify
    (lambda (t v)
      (match t
        [(Base _) v]
        [(Prod t1 t2)
         `(cons ,(reify t1 (car v))
                ,(reify t2 (cdr v)))]
        [(Func t1 t2)
         (let ([x1 (fresh-name 'x)])
           `(lambda (,x1)
              ,(reset (reify t2 (v (reflect t1 x1))))))] ;; Note: here needs a reset, which was missing in the paper
        [(Proc t1 t2)
         (let ([x1 (fresh-name 'x)])
           `(lambda (,x1)
              ,(reset (reify t2 (v (reflect t1 x1))))))])))

  (define reflect
    (lambda (t e)
      (match t
        [(Base _) e]
        [(Prod t1 t2)
         (cons (reflect t1 `(car ,e))
               (reflect t2 `(cdr ,e)))]
        [(Func t1 t2)
         (lambda (v1)
           (reflect t2 `(,e ,(reify t1 v1))))]
        [(Proc t1 t2)
         (lambda (v1)
           (let ([q2 (fresh-name 'x)])
             (shift k
                    `(let ([,q2 (,e ,(reify t1 v1))])
                       ,(reset (k (reflect t2 q2)))))))])))

  (define residualize
    (lambda (v t)
      (begin
        (set! count 0)
        (reify (parse-type t) v))))

  (define make-power
    ;; int -> (a -> a) * (a * a -> a) -> a -> a
    (lambda (n)
      (lambda (sqr)
        (lambda (mul)
          (lambda (x)
            (letrec ([visit (lambda (n)
                              (if (zero? n) 1
                                  (visit-positive n)))]
                     [visit-positive (lambda (m)
                                       (if (even? m)
                                           (sqr (visit-positive (quotient m 2)))
                                           ((mul (sqr (visit (quotient m 2)))) x)))])
              (visit n)))))))

  )

(displayln "let-inserted residualization")

(require (prefix-in let: '5-2-7))

(let:residualize
 (let:make-power 10)
 '((a -!> a) -> (a -> a -!> a) -> a -> a))

;; The result is alpha-equivalent to:

'(lambda (sqr)
   (lambda (mul)
     (lambda (x2)
       (let ([x3 (sqr 1)]
             [x4 ((mul x3) x2)]
             [x5 (sqr x4)]
             [x6 (sqr x5)]
             [x7 ((mul x6) x2)]
             [x8 (sqr x7)]
             x8)))))
