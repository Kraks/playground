#lang racket

(require math/base)

(define current-continuation
  (λ () (call/cc (lambda (cc) (cc cc)))))

(define fail-stack '())

(define (fail)
  (if (not (pair? fail-stack))
      (error "back-tracking stack exhausted!")
      (let ([back-track-point (car fail-stack)])
        (set! fail-stack (cdr fail-stack))
        (back-track-point back-track-point))))

(define (amb choices)
  (let ([cc (current-continuation)])
    (cond [(null? choices) (fail)]
          [(pair? choices)
           (let ([choice (car choices)])
             (set! choices (cdr choices))
             (set! fail-stack (cons cc fail-stack))
             choice)])))

(define (require pred) (if (not pred) (fail) #t))

;;;;;;;;;;;;;;

(define (transpose grid)
    (if (null? grid) '()
        (map (λ (i) (map (λ (line) (list-ref line i)) grid))
             (range (length (car grid))))))

(define (aux-diag mat)
  (for/list ([i (range 0 (length mat))])
    (list-ref (list-ref mat i) i)))

(define (make-grid n)
  (make-list n (make-list n (amb '(0 1)))))

#|
(let ([g (make-grid 4)])
  (for/list ([line g])
    (require (= 1 (sum line))))
  (for/list ([line (transpose g)])
    (require (= 1 (sum line))))
  (for/list ([line
|#