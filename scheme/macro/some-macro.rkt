#lang racket

(define-syntax (my-let stx)
  (syntax-case stx ()
    [(my-let (var val) body)
     (identifier? #'var)
     #'((lambda (var) body) val)]))

(define-syntax (myor stx)
  (syntax-case stx ()
    [(myor) #'#f]
    [(myor e) #'e]
    [(myor e0 e1 ...)
     #'(let ([v e0])
         (if v v
             (myor e1 ...)))]))

;; CPS

(define-syntax (cps e)
  (syntax-case e (with rec lam cnd seq set quote display read-number)
    [(_ (with (v e) body))
     #'(cps ((lam (v) body) e))]
    [(_ (rec (v f) body))
     #'(cps (with (v (lam (arg) (error 'dummy "nothing")))
                  (seq (set v f) body)))]
    [(_ (lam (a) b))
     (identifier? #'a)
     #'(lambda (k)
         (k (lambda (a dyn-k)
              ((cps b) dyn-k))))] ;; Using the continuation where the closure invoked
    [(_ (cnd tst thn els))
     #'(lambda (k)
         ((cps tst) (lambda (tstv
                             (if tstv
                                 ((cps thn) k)
                                 ((cps els) k))))))]
    [(_ (display output))
     #'(lambda (k)
         ((cps output) (lambda (ov)
                         (k (display ov)))))]
    [(_ (seq e1 e2))
     #'(lambda (k)
         ((cps e1) (lambda (_) ((cps e2) k))))]
    [(_ (set v e))
     #'(lambda (k) ((cps e) (lambda (ev) (k (set! v ev)))))]
    [(_ (generator (yield) (v) b))
     (and (identifier? #'v) (identifier? #'yield))
     #'(lambda (k)
         (k (let ([where-to-go (lambda (v) (error 'where-to-go "nothing"))])
              (letrec ([resumer (lambda (v)
                                  ((cps b) (lambda (k)
                                             (error 'generator "fell through"))))]
                       [yield (lambda (v gen-k)
                                (begin (set! resumer gen-k)
                                       (where-to-go v)))])
                (lambda (v dyn-k)
                  (begin
                    (set! where-to-go dyn-k)
                    (resumer v)))))))]
    [(_ 'e)
     #'(lambda (k) (k 'e))]
    [(_ (f a))
     #'(lambda (k)
         ((cps f) (lambda (fv)
                    ((cps a) (lambda (av)
                               (fv av k))))))]
    [(_ (f a b))
     #'(lambda (k)
         ((cps a) (lambda (av)
                    ((cps b) (lambda (bv)
                               (k (f av bv)))))))]
    [(_ atomic)
     #'(lambda (k) (k atomic))]))

(define (run c) (c (λ (x) x)))

;; Generator

(define-syntax let/cc
  (syntax-rules ()
    [(let/cc k b)
     (call/cc (lambda (k) b))]))

(define-syntax (generator e)
  (syntax-case e ()
    [(generator (yield) (v) body)
     #'(let ([where-to-go (λ (v) (error 'where-to-go "nothing"))])
         (letrec ([resumer (λ (v) (begin body (error 'generator "fell through")))]
                  [yield (λ (v) (let/cc gen-k
                                  (begin (set! resumer gen-k)
                                         (where-to-go v))))])
           (λ (v)
             (let/cc dyn-k
               (begin (set! where-to-go dyn-k)
                      (resumer v))))))]))

(define g1 (generator (yield) (v)
                      (letrec ([loop (lambda (n)
                                       (begin
                                         (yield n)
                                         (loop (+ n 1))))])
                        (loop v))))
