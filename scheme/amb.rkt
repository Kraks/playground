#lang racket

(display
 (call/cc (lambda (cc)
            (display "I got here\n")
            (cc "This is sting was passed to the continuation\n")
            (display "But not here\n"))))

(define (current-continuation)
  (call/cc (lambda (cc) (cc cc))))

; A idiom of continuation
;(let ((cc (current-continuation)))
;  (cond 
;    ((continuation? cc) body)
;    ((future-value? cc) handling-body)
;    (else (error "Contract violation"))))

;; (right-now) returns the current moment in the computation
;; (go-when) returns the computation to a previously captured moment

; right-now : -> moment
(define (right-now)
  (call-with-current-continuation
   (lambda (cc)
     (cc cc))))

; go-when : moment -> ...
(define (go-when then)
  (then then))

;; implementation of amb

; fail-stack : list[continuation]
(define fail-stack '())

; fail : -> ...
(define (fail)
  (if (not (pair? fail-stack))
      (error "back-tracking stack exhuasted!")
      (begin
        (let ((back-track-point (car fail-stack)))
          (set! fail-stack (cdr fail-stack))
          (back-track-point back-track-point)))))

; amb : list[a] -> a
(define (amb choices)
  (let ((cc (current-continuation)))
    (cond ((null? choices) (fail))
          ((pair? choices)
           (let ((choice (car choices)))
             (set! choices (cdr choices))
             (set! fail-stack (cons cc fail-stack))
             choice)))))

