#lang racket

#| Id Monad |#

; return/id : a -> a
(define return/id (λ (a) a))
; bind/id : a -> (a -> b) -> b
(define bind/id (λ (ma f) (f ma)))

(define plus/id
  (λ (a b)
    (bind/id (return/id (+ a b))
             (λ (x) (return/id x)))))

#| Maybe Monad |#

(struct Just (a)   #:transparent)
(struct Nothing () #:transparent)

; return/maybe : a -> Maybe a
(define return/maybe
  (λ (a) (Just a)))

; bind/maybe: Maybe a -> (a -> Maybe b) -> Maybe b
(define bind/maybe
  (λ (ma f)
    (match ma
      [(Just a) (f a)]
      [(Nothing) (Nothing)])))

(define fail
  (λ () (Nothing)))

; int -> int -> Maybe rat
(define div/maybe
  (λ (a b)
    (if (zero? b) (fail)
        (return/maybe (/ a b)))))

(bind/maybe
 (return/maybe (+ 7 8))
 (λ (x) (bind/maybe
         (div/maybe x 4)
         (λ (x^)
           (return/maybe x^)))))

#| Do Syntax |#

(define-syntax do
  (syntax-rules (<-)
    [(_ bind e) e]
    [(_ bind (v <- e0) e e* ...)
     (bind e0 (λ (v) (do bind e e* ...)))]
    [(_ bind e0 e e* ...)
     (bind e0 (λ (_) (do bind e e* ...)))]))

(do bind/maybe
  (x <- (return/maybe (+ 7 8)))
  (x^ <- (div/maybe x 4))
  (return/maybe x^))

#| Write Monad |#

(define return/writer
  (λ (a) `(,a . ())))

(define bind/writer
  (λ (ma f)
    (let ([mb (f (car ma))])
      `(,(car mb) . ,(append (cdr ma) (cdr mb))))))

(define tell/writer
  (λ (to-write)
    `(_ . (,to-write))))

(define reciprocals
  (λ (l)
    (cond [(null? l) (return/writer '())]
          [(zero? (car l))
           (bind/writer
            (tell/writer "saw a 0")
            (λ (_) (reciprocals (cdr l))))]
          [else
           (bind/writer
            (reciprocals (cdr l))
            (λ (d)
              (return/writer
               (cons (/ 1 (car l)) d))))])))

(define reciprocals2
  (λ (l)
    (cond [(null? l) (return/writer '())]
          [(zero? (car l))
           (do bind/writer
             (tell/writer "saw a 0")
             (reciprocals2 (cdr l)))]
          [else
           (do bind/writer
             (d <- (reciprocals2 (cdr l)))
             (return/writer (cons (/ 1 (car l)) d)))])))

#| State Monad |#

(define return/state
  (λ (a)
    (λ (s)
      `(,a . ,s))))

(define bind/state
  (λ (ma f)
    (λ (s)
      (let ([vs (ma s)])
        (let ([v (car vs)]
              [s^ (cdr vs)])
          ((f v) s^))))))

(define get/state
  (λ (s)
    `(,s . ,s)))

(define put/state
  (λ (new-s)
    (λ (s)
      `(_ . ,new-s))))

(define even-length?
  (λ (l s)
    (cond [(null? l) s]
          [else (even-length? (cdr l) (not s))])))

(define even-length2?
  (λ (l)
    (cond [(null? l) (return/state '_)]
          [else (do bind/state
                  (s <- get/state)
                  (put/state (not s))
                  (even-length2? (cdr l)))])))
