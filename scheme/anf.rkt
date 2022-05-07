#lang racket

(define (fact n)
  (if (= 0 n)
      1
      (* n (fact (- n 1)))))

(define (fact-cps n k)
  (if (= 0 n)
      (k 1)
      (fact-cps (- n 1) (λ (v) (k (* n v))))))

(fact 5)
(fact-cps 5 (λ (x) x))

(define (normalize e k)
  (match e
    [(? number? n) (k n)]
    [(? symbol? x) (k x)]
    [`(lambda (,x) ,e0)
     (k `(lambda (,x) ,(anf-convert e0)))]
    [`(if ,e0 ,e1 ,e2)
     (normalize-ae e0 (λ (ae0)
                        (k `(if ,ae0 ,(anf-convert e1) ,(anf-convert e2)))))]
    [`(,es ...)
     (normalize-aes es k)]))

(define (normalize-ae e k)
  (normalize e (λ (anf)
                 (match anf
                   [(? number? n) (k n)]
                   [(? symbol? x) (k x)]
                   [`(lambda ,xs ,e0)
                    (k `(lambda ,xs ,e0))]
                   [else
                    (define x (gensym 'x))
                    `(let ([,x ,anf])
                       ,(k x))]))))

(define (normalize-aes es k)
  (if (null? es)
      (k '())
      (normalize-ae (first es)
                    (λ (ae)
                      (normalize-aes (rest es) (λ (aes) (k (cons ae aes))))))))

(define (anf-convert e)
  (normalize e (λ (x) x)))

(define fib
  '(if (<= n 1)
      n
      (+ (fib (- n 1)) (fib (- n 2)))))

(anf-convert fib)

'(let ((x23311 (<= n 1)))
   (if x23311
     n
     (let [(x23312 (- n 1))]
       (let ((x23313 (fib x23312)))
         (let ((x23314 (- n 2)))
           (let ((x23315 (fib x23314)))
             (+ x23313 x23315)))))))