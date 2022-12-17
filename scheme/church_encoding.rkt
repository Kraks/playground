#lang racket

(define-syntax print-test
  (syntax-rules ()
    ((_ exp)
     (begin
       (write (quote exp))
       (display " == ")
       (write exp)
       (newline)))))

;; curry2 : (A B -> C) -> (A -> B -> C)
(define curry2
  (lambda (f)
    (lambda (x)
      (lambda (y)
        (f x y)))))

;; f : num num -> num
(define f
  (lambda (x y)
    (+ x y)))

;; f^C : num -> num -> num
(define f^C
  (curry2 f))

;; void : void
(define void
  (lambda (x) x))

;; error : (-> *)
(define error
  (lambda ()
    ((lambda (f) (f f))
     (lambda (f) (f f)))))

;; true : boolean
(define true
  (lambda (on-true on-false)
    (on-true)))

;; false : boolean
(define false
  (lambda (on-true on-false)
    (on-false)))

;; if! : boolean A A -> A
(define if!
  (lambda (condition true-value false-value)
    (condition
     (lambda () true-value)
     (lambda () false-value))))

(if! true 't 'f)
(if! false 't 'f)

;; if* : boolean (-> A) (-> A) -> A
(define if*
  (lambda (condition on-true on-false)
    (condition on-true on-false)))

(print-test
 (if* true
      (lambda () 42)
      (lambda () 123)))

(print-test
 (if* false
      (lambda () 42)
      (lambda () 123)))

;; nil : List[*]
(define nil
  (lambda (on-null on-pair)
    (on-null)))

;; kons : A List[A] -> List[A]
(define kons
  (lambda (a b)
    (lambda (on-null on-pair)
      (on-pair a b))))

;; kar : List[A] -> A
(define kar
  (lambda (list)
    (list (lambda () (error))
          (lambda (a b) a))))

;; kdr : List[A] -> List[A]
(define kdr
  (lambda (list)
    (list (lambda () (error))
          (lambda (a b) b))))

;; match-list : List[A] (-> B) (A List[A] -> B) ->B
(define match-list
  (lambda (list on-null on-pair)
    (list on-null on-pair)))

;; kons? : List[A] -> boolean
(define kons?
  (lambda (list)
    (list (lambda () #f)
          (lambda (a b) #t))))

;; nul? : List[A] -> boolean
(define nil?
  (lambda (list)
    (list (lambda () #t)
          (lambda (a b) #f))))

(print-test (car (cdr (cons 3 (cons 4 '())))))
(print-test (kar (kdr (kons 3 (kons 4 nil)))))

(print-test
 (match-list (kons 3 4)
             (lambda () void)
             (lambda (a b) a)))

;; A Church numeral applies its first argument to its 
;; second argument n times.
;; n(f)(x) == f^n(x)
;; number = (A -> A) -> A -> A

;; zero : number
(define zero
  (lambda (f)
    (lambda (zero)
      zero)))

;; succ : number -> number
(define succ
  (lambda (n)
    (lambda (f)
      (lambda (x)
        ((n f) (f x))))))

;; one
(define one (succ zero))
(lambda (f)
  (lambda (x)
    ((zero f) (f x))))

;; two 
(define two (succ one))
(lambda (f)
  (lambda (x)
    ((one f) (f x))))

;; add : number number -> number
(define add 
  (lambda (n m)
    (lambda (f)
      (lambda (x)
        ((n f) ((m f) x))))))

;; mul : number number -> number
(define mul
  (lambda (n m)
    (lambda (f)
      (lambda (x)
        ((m (n f)) zero)))))

;; inc : num -> num
(define inc
  (lambda (z) (+ z 1)))

(print-test
 (((succ zero) inc) 0))

(print-test
 (((lambda (f)
     (lambda (x)
       ((one f) (f x)))) inc) 0))

(print-test
 (((add one one) inc) 0))

;; TODO
;;(print-test
;; (((mul two two) inc) 0))

;; The U combinator passes its argument to itself, 
;; enabling self-reference.
; (U F) = (F F)

(define U
  (lambda (F) (F F)))

; The Y Combinator computes the fixed point of a functional:
; (Y F) = (F (Y F))
; (Y F) = (F (Y F))
;  Y = (lambda (F) (F (Y F)))
;    = (lambda (F) (F (F (F (Y F)))))
;    = (lambda (F) (F (lambda (x) ((Y F) x))))
;    = (U (lambda (y) (lambda (F) (F (lambda (x) (((y y) F) x))))))
;    = ((lambda (y) (lambda (F) (F (lambda (x) (((y y) F) x)))))
;       (lambda (y) (lambda (F) (F (lambda (x) (((y y) F) x))))))

(define Y
  ((lambda (y) (lambda (F) (F (lambda (x) (((y y) F) x)))))
   (lambda (y) (lambda (F) (F (lambda (x) (((y y) F) x)))))))

(define U-fact (U (lambda (f)
                    (lambda (n)
                      (if (<= n 0) 1
                          (* n ((U f) (- n 1))))))))

(define Y-fact (Y (lambda (f)
                    (lambda (n)
                      (if (<= n 0) 1
                          (* n (f (- n 1))))))))

; map : (A -> B) list[A] -> list[B]
(define (map f lst)
  (if (pair? lst)
      (cons (f (car lst))
            (map f (cdr lst)))
      '()))

; foldr : (A B -> B) B List[A] -> B
(define (foldr f nil lst)
  (if (pair? lst)
      (f (car lst)
         (foldr f nil (cdr lst)))
      nil))

(print-test (foldr (lambda (x y) (+ x y)) 0
                   (list 1 2 3 4 5)))

; range : num num -> list[num]
(define (range lo hi)
  (if (<= lo hi)
      (cons lo (range (+ lo 1) hi))
      '()))
