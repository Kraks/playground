#lang racket

(require racket/control)

(+ (reset (+ 3 (* 5 2))) 1) ; => 14

(reset (- (+ 3 (shift _ (* 5 2))) 1))

(+ 1 (reset (+ 1 (shift _ (* 5 2)))))

(reset (- (+ 3 (shift _ "hello")) 1)) ; context = 3 + [-] - 1 : int -> int

(string-append
 (reset (if (shift _ "what ")
            "hello"
            "hi"))
 "world")

(car (reset (let ([x (shift _ (cons 1 2))])
              (cons 3 4))))

(define (times xs)
  (match xs
    [(list) 1]
    [(list x xs^ ...)
     (* x (times xs^))]))

(define (times-naive xs)
  (match xs
    [(list) 1]
    [(list 0 xs^ ...)
     0]
    [(list x xs^ ...)
     (* x (times-naive xs^))]))

(define (times-dc xs)
  (match xs
    [(list) 1]
    [(list 0 xs^ ...)
     (shift _ 0)]
    [(list x xs^ ...)
     (* x (times-dc xs^))]))

(reset (times-dc (list 1 2 3 0 4)))

(define (f x)
  ((reset (- (+ 3 (shift k k)) 1)) x))

(f 10)

(define (id-list xs)
  (match xs
    [(list) (list)]
    [(list x xs^ ...)
     (cons x (id-list xs^))]))

(id-list (list 1 2 3))

(define (id-list-dc xs)
  (match xs
    [(list) (shift k k)] ; k : a list -> a list
    [(list x xs^ ...)
     (cons x (id-list-dc xs^))]))

(define cons123 (reset (id-list-dc (list 1 2 3))))

(cons123 (list 4 5 6))