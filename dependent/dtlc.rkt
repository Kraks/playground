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

(define (fun0? f) (procedure? f))

(define (fun0 f)
  (assert (fun0? f))
  f)

(define (app0 f a)
  (if (fun0? f) (f a)
      (list f a)))

(define (forall0 atp f) (list 'forall atp f))

(define (forall0? f) (and (list? f) (equal? (first f) 'forall)))

(define (typed e t) (list 'typed e t))
(define (typed? e)
  (and (list? e) (equal? (first e) 'typed)))
(define (untyped e)
  (assert (typed? e) "no type of e")
  (rest e))

(define (forall atp f)
  (match atp
    [(list _ atpt atpk)
     (assert (or (equal? atpk 'Type)
                 (equal? atpk 'Kind)))
     (define restpe (untyped (f (typed 'x? atpt))))
     (define res (first restpe))
     (define tpe (second restpe))
     (typed (forall0 atpt (λ (x) (first (untyped (f (typed x atpt))))))
            tpe)]))

(define (fun atp f)
  (match atp
    [(list _ atpt atpk)
     (assert (or (equal? atpk 'Type)
                 (equal? atpk 'Kind)))
     (typed (fun0 (λ (x) (first (untyped (f (typed x atpt))))))
            (forall0 atpt (λ (x) (second (untyped (f (typed x atpt)))))))]))

(define (app f a)
  (match* (f a)
    [((list _ f1 ftp) (list _ a1 atp))
     (assert (forall0? ftp))
     (match ftp
       [(list key ptp frtp)
        (assert (equal? (stringify atp) (stringify ptp)))
        (typed (app0 f1 a1) (frtp a1))])]))

(define (constant tm ty)
  (match ty
    [(list _ tyt tyk)
     (assert (or (equal? tyk 'Type)
                 (equal? tyk 'Kind)))
     (typed tm tyt)]))

(define Type (typed 'Type 'Kind))

(define (print-term e)
  (match e
    [(list _ tm ty)
     (displayln (format "term: ~a" (stringify tm)))
     (displayln (format "type: ~a" (stringify ty)))]))

;; identity functions

(define typeId (fun Type (λ (x) x)))
(print-term typeId)

(define polyId (fun Type (λ (t) (fun t (λ (x) x)))))
(print-term polyId)

(define polyId2 (fun Type (λ (t) (fun t (λ (x) (app (fun t (λ (y) y)) x))))))
(print-term polyId2)

;; numbers

(define N (constant 'N Type))
(define z (constant 'z N))
(define s (constant 's (forall N (λ (x) N))))
(define three (app s (app s (app s z))))
(print-term three)

(define ff (λ (T) (forall T (λ (x) T))))
(define ChurchT
  (forall Type (λ (N) (forall N (λ (z) (forall (ff N) (λ (s) N)))))))
(define ChurchN
  (λ (f) (fun Type
              (λ (N) (fun N
                          (λ (z) (fun (ff N)
                                      (λ (s) (((f N) z) s)))))))))
(define peano (fun ChurchT (λ (n) (app (app (app n N) z) s))))
(print-term peano)
(define three^ (ChurchN (λ (N) (λ (z) (λ (s) (app s (app s (app s z))))))))
(print-term three^)
(print-term (app peano three^))