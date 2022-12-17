#lang racket

;(provide empty union fixed-point fix let*/set join setof)
(require syntax/parse/define)

(define empty (set))
(define (union . xs) (apply set-union (set) xs))

(define (fixed-point f #:init [init (set)])
  (define next (f init))
  (if (equal? init next) init
      (fixed-point f #:init next)))

(define-simple-macro (fix (x:id) M:expr ...)
  (fixed-point (lambda (x) (union M ...))))

(define-simple-macro (let*/set (for-clause ...) body ...+)
  (for*/set (for-clause ... [result (begin body ...)]) result))

#|
(for*/set ([x (set 1 2 3)]
           [y (set 1 2 3)])
  (+ x y))

(let*/set
 ([x (set 1 2 3)]
  [y (set 1 2 3)])
 (set (+ x y)))

(for*/set
    ([x (set 1 2 3)]
     [y (set 1 2 3)]
     [result (+ x y)])
  result)
|#

(begin-for-syntax
  (define-syntax-class definition
    #:literals (define)
    (pattern (define stuff ...))))

;; (join L ... M)
(define-syntax-parser join
  #:datum-literals (<-)
  #:literals (when)
  [(join body:expr) #'body]
  [(join d:definition ...+ body ...+)
   #'(local (d ...) (join body ...))]
  [(join (x:id <- M:expr) ...+ L ...+)
   #'(let*/set ([x M] ...) (join L ...))]
  [(join (p <- M:expr) L ...+)
   #'(let*/set ([tmp M])
               (match tmp [p (join L ...)] [_ (set)]))]
  [(join (when condition:expr) L ...+)
   #'(if condition (join L ...) (set))])

(define-simple-macro (setof M:expr L ...) (join L ... (set M)))

;; Examples

(define (smap f S)
  (setof (f x) (x <- S)))

(smap (lambda (x) (+ x 1)) (set 1 2 3))

(define (sfilter p S)
  (setof x
         (x <- S)
         (when (p x))))

(sfilter (lambda (x) (> x 0)) (set -1 2 -2 3))

(define (cross A B)
  (setof (list a b)
         (a <- A)
         (b <- B)))

(cross (set 1 2 3) (set 2 3 4))

(define (interesect A B)
  (setof x
         (x <- A)
         (y <- B)
         (when (equal? x y))))

(define (intersect-variant A B)
  (setof x
         (x <- A)
         ((== x) <- B)))