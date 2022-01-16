#lang racket

(define n-vars 0)
(define (fresh)
  (define n (+ n-vars 1))
  (set! n-vars n)
  (string->symbol (string-append "x" (number->string n))))

(define (struct e)
  (match e
    [(? list?) (map struct e)]
    [(? procedure?)
     (define x (fresh))
     `(=> ,x ,(struct (e x)))]
    [else e]))

(define (stringify e)
  (define n n-vars)
  (define r (struct e))
  (set! n-vars n)
  r)

(define-syntax assert
  (syntax-rules ()
    [(assert e)
     (match e
       [#t #t]
       [#f (error 'assert "assertion violates")])]
    [(assert e msg)
     (match e
       [#t #t]
       [#f (error 'assert msg)])]))

(define fun? procedure?)
(define (fun0 f)
  (match f
    [(? fun?) f]
    [else (error 'fun0 "not a function")]))
(define (app0 f a)
  (if (fun? f) (f a)
      (list f a)))

(define base-type? symbol?)
(define (fun-type? t)
  (and (list? t)
       (equal? (first t) '->)))
(define (type? t)
  (or (base-type? t) (fun-type? t)))

(define (fun-type atp rtp)
  (assert (type? atp) "illegal arg type")
  (assert (type? rtp) "illegal rtp type")
  (list '-> atp rtp))

(define (typed e t)
  (list 'typed e t))
(define (typed? e)
  (and (list? e) (equal? (first e) 'typed)))
(define (untyped e)
  (assert (typed? e) "no type of e")
  (rest e))

(define (print-term e)
  (match e
    [(list _ tm ty)
     (displayln (format "term: ~a" (stringify tm)))
     (displayln (format "type: ~a" (stringify ty)))]))

(define (fun atp f)
  (assert (type? atp) "illegal arg type")
  (typed (fun0 (λ (x) (first (untyped (f (typed x atp))))))
         (fun-type atp (second (untyped (f (typed 'x? atp)))))))

(define (app f a)
  (match* (f a)
    [((list _ f1 (list '-> ptp rtp)) (list _ a1 atp))
     (assert (equal? ptp atp) "argument types mismatch")
     (define res (app0 f1 a1))
     (typed res rtp)]))

(define (constant tm ty)
  (assert (type? ty))
  (typed tm ty))

(define intId (fun 'int (λ (x) x)))
(print-term intId)

(define eta (fun (fun-type 'int 'int)
                 (λ (f) (fun 'int (λ (x) (app f x))))))
(print-term eta)

(define etaIntId (app eta (fun 'int (λ (x) x))))
(print-term etaIntId)