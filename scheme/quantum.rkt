#lang racket

;; Code from Scheme Pearl: Quantum Continuations
;; by Choudhury, Agapiev, and Sabry, Scheme workshop 2022

(require racket/control)
(require racket/hash)
(require racket/vector)

;; Recap: nondeterministic choice via shift/reset

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

; upd : Vec[X], int, (X -> X): Vec[X]
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

;; Toffoli gate, or Controlled-Controlled-Not gate
; If the first two bits are set, then it negates the third bit;
; all other input bits are preserved otherwise.
; Using Toffoli gate, we can implement any boolean function in a reversible way.

(define-syntax-rule (CCX a b c) `(ccx ,a ,b ,c))

;; Hadamard gate
; A single-qubit operation that maps the basic state
; |0⟩ to (|0⟩ + |1⟩) / √2, and 
; |1⟩ to (|0⟩ - |1⟩) / √2.
; It creates an equal superposition of the two basic states.

;; But what is superposition?
; Two (or more) quantum states can be added (superposed), and the result is another
; valid quantum state. Conversely, every quantum state can be represented
; as a sum of two (or more) other distinct states.

(define-syntax-rule (H a) `(h ,a))

; Not gate by using Toffoli gate

(define-syntax-rule (X a) (CCX #t #t a))

;; Controlled-not gate
; If a is 0, then in the output b is preserved.
; If a is 1, then in the output b is negated.

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

(define (evalg^ v g)
  (match `(,v ,g)
    [`((,d ,bs) (ccx ,ctrl1 ,ctrl2 ,tgt))
     #:when (and (is-set? bs ctrl1)
                 (is-set? bs ctrl2))
     `(,d ,(neg bs tgt))]
    [`((,d ,bs) (ccx ,ctrl1 ,ctrl2 ,tgt))
     `(,d ,bs)]
    [`((,d ,bs) (h ,tgt))
     #:when (is-set? bs tgt)
     (collect^ `(,(* hscale d) ,(neg bs tgt))
               `(,(* -1.0 hscale d) ,bs))]
    [`((,d ,bs) (h ,tgt))
     (collect^ `(,(* hscale d) ,bs)
               `(,(* hscale d) ,(neg bs tgt)))]
    [_ (error "evalg^: invalid arguments")]))

(define (evalc^ v c)
  (foldl (λ (g st) (evalg^ st g)) v c))