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

;; reset == prompt
;; shift == control

(reset (shift e (displayln "get there"))
       (displayln "never reach here"))

(reset (define x (shift k
                        (k 1)
                        (k 5)
                        (k 25)))
       (printf "shift ~a\n" x))

(reset (define x (shift k (displayln (k 42))))
       "here is the continuation")

;;;;;;;;;;;;;

(prompt (control k (displayln "get there"))
        (display "never reach here"))

(prompt (define x (control k
                           (k 1)
                           (k 5)
                           (k 25)))
        (printf "shift ~a\n" x))

(prompt (define-values (x y)
          (control k (displayln (k 1 2))))
        "here is the continuation"
        x
        y)

;;;;;;;;;;;;

(prompt (+ 2 (control k (k 5))))

(+ 2 (prompt (+ 2 (control k 5))))

(prompt (+ 2 (control k (+ 1 (control k1 (k1 6))))))

(prompt (+ 2 (control k (+ 1 (control k1 (k 6))))))

(prompt (+ 2 (control k (control k1 (control k2 (k2 6))))))

;;;;;;;;;;;

; Multi-prompt continuations

(define tag-a (make-continuation-prompt-tag 'a))
(define tag-b (make-continuation-prompt-tag 'b))

(reset-at
 tag-a
 (+ 10 (shift-at tag-a k (+ 1 (k 3)))))

; kb = λv. v+5+10+111
; ka = λv. v+10

;    (ka (kb 3))
; => (3 + 5 + 10 + 111) + 10
(reset-at
 tag-b
 (+ 111
    (reset-at
     tag-a
     (+ 10 (shift-at tag-a ka
                     (+ 5 (shift-at tag-b kb
                                   (ka (kb 3)))))))))

; (ka 3) => 3 + 10
(reset-at
 tag-b
 (+ 111
    (reset-at
     tag-a
     (+ 10 (shift-at tag-a ka
                     (+ 5 (shift-at tag-b kb
                                    (ka 3))))))))