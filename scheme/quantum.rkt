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

; hscale = 1/√2 = 0.7071...
(define hscale (/ 1.0 (sqrt 2.0)))

(define (is-set? v i)
  (cond [(nonnegative-integer? i) (vector-ref v i)]
        [(boolean? i) i]
        [else (error "is-set?: invalid index")]))

;; Toffoli gate, or Controlled-Controlled-Not gate
; If the first two bits are set, then it negates the third bit;
; all other input bits are preserved otherwise.

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
; When measure a qubit in a superposition state of equal weights,
; it collapse to one of its two basis states |0⟩ and |1⟩ with an equal probability.

; A quantum computer consisting of n qubits can exist in a superposition
; of 2^n states: |000⋯0⟩ to |111⋯1⟩.

(define-syntax-rule (H a) `(h ,a))

;; Not gate by using Toffoli gate
; Since the first and second bit are set, the output is the negation of a.

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

; Gate evaluator
; v = (d bs) where d is the probability amplitude
; and bs is a bit-vector representation of states.

(define (evalg^ v g)
  (match `(,v ,g)
    ; Toffoli gate:
    ; If ctrl1 and ctrl2 are set, negates tgt
    [`((,d ,bs) (ccx ,ctrl1 ,ctrl2 ,tgt))
     #:when (and (is-set? bs ctrl1)
                 (is-set? bs ctrl2))
     `(,d ,(neg bs tgt))]
    ; Toffoli gate:
    ; otherwise nothing changes
    [`((,d ,bs) (ccx ,ctrl1 ,ctrl2 ,tgt))
     `(,d ,bs)]
    ; Hadamard gate with target bit set
    ; We negate the amplitude and multiply it with -1.0
    [`((,d ,bs) (h ,tgt))
     #:when (is-set? bs tgt)
     (collect^ `(,(* hscale d) ,(neg bs tgt))
               `(,(* -1.0 hscale d) ,bs))]
    ; Hadamard gate with target bit unset
    [`((,d ,bs) (h ,tgt))
     (collect^ `(,(* hscale d) ,bs)
               `(,(* hscale d) ,(neg bs tgt)))]
    [_ (error "evalg^: invalid arguments")]))

; Circuit evaluator

(define (evalc^ v c)
  (foldl (λ (g st) (evalg^ st g)) v c))

; Top-level runner of circuit

(define (run-circ t circ st)
  (reset
   (match (evalc^ st circ)
     [`(,d ,bs)
      (match t
        [`list (list `(,bs ,d))]
        [`hash (hash bs d)]
        [_ (error "run-circ: invalid tag")])])))

; Pretty printer

(define (pretty-vec bs)
  (string-append
   "|"
   (foldl (λ (b s) (string-append (if b "1" "0") s))
          "⟩"
          (vector->list bs))))

(define (pretty-prob d)
  (~r d #:sign '+ #:precision '(= 2)))

(define (pretty-state st)
  (cond
    [(list? st)
     (for-each
      (match-lambda*
        [`((,bs ,d)) #:when (< (abs d) 0.01) (void)]
        [`((,bs ,d)) (printf "(~a~a)~n" (pretty-prob d)(pretty-vec bs))])
      st)]
    [(hash? st)
     (hash-for-each
      st
      (match-lambda*
        [`(,bs ,d) #:when (< (abs d) 0.01) (void)]
        [`(,bs ,d) (printf "(~a~a)~n" (pretty-prob d)(pretty-vec bs))]))]
    [else (error "pretty-state: unknown state")]))

; Example 1

(define circuit1
  (list (H 0)
        (CX 0 1)))

; expect (+0.71|00⟩) (+0.71|11⟩)
;(pretty-state (run-circ `list circuit1 `(1.0 ,(make-vector 2 #f))))

; Example 2

(define circuit2
  (list (H 0)
        (X 0)
        (H 0)))

; expect (+0.50|0⟩) (-0.50|1⟩) (+0.50|0⟩) (+0.50|1⟩)
;(pretty-state (run-circ `list circuit2 `(1.0 ,(make-vector 1 #f))))

;(pretty-state (run-circ `hash circuit2 `(1.0 ,(make-vector 1 #f))))

; Example - Simon's Problem
; Given a two-to-one function f: B^n -> B^n with the property
; that there exists an `a` such that f(x) = f(x xor a), the
; problem is the find such `a`.

(define simon-circuit
  (list (H 0)
        (H 1)
        (CX 0 2)
        (CX 0 3)
        (CX 1 2)
        (CX 1 3)
        (H 0)
        (H 1)))

;(pretty-state (run-circ `list simon-circuit `(1.0 ,(make-vector 4 #f))))

(pretty-state (run-circ `hash simon-circuit `(1.0 ,(make-vector 4 #f))))
