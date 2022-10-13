#lang racket

;; Code from Scheme Pearl: Quantum Continuations

(require racket/control)
(require racket/hash)
(require racket/vector)

;; nondeterministic choice via shift/reset

(define (choose^ a b)
  (shift k (append (k a) (k b))))

(define expr
  (reset (let ([x (choose^ 1 2)]
               [y (choose^ 3 4)])
           (list (+ x (* 5 y))))))

(reset (let ([x (shift k (k 1) (k 2))]
             [y (shift k (k 3) (k 4))])
         (displayln (+ x (* 5 y)))))

;; vector and hash helper functions

(define (upd v i f)
  (let ([w (vector-copy v)])
    (vector-set! w i (f (vector-ref w i)))
    w))

(define (neg v i) (upd v i not))

(define hscale (/ 1.0 (sqrt 2.0)))

(define (is-set? v i)
  (cond [(nonnegative-integer? i) (vector-ref v i)]
        [(boolean? i) i]
        [else (error "is-set?: invalid index")]))

; Toffoli gate

(define-syntax-rule (CCX a b c) `(ccx ,a ,b ,c))

; Hadamard gate

(define-syntax-rule (H a) `(h ,a))

; Not gate by using Toffoli gate

(define-syntax-rule (X a) (CCX #t #t a))

; Controlled-not gate

(define-syntax-rule (CX a b) (CCX #t a b))

; collect^ operation

(define (collect^ x y)
  (shift
   k
   (let ([a (k x)]
         [b (k y)])
     (cond [(and (list? a) (list? b)) (append a b)]
           [(and (hash? a) (hash? b)) (hash-union a b #:combine +)]
           [else (error "collect^: unknown state")]))))

; gate and circuit evaluator

