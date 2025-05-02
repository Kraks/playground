#lang racket

(define (cps-convert term cont)
  (match term
    [`(,f ,e)
     (let (($f (gensym 'f))
           ($e (gensym 'e)))
       (cps-convert f `(lambda (,$f)
                         ,(cps-convert e `(lambda (,$e)
                                            (,$f ,$e ,cont))))))]
    [`(lambda (,v) ,e)
     (let (($k (gensym 'k)))
       `(,cont (lambda (,v ,$k)
                 ,(cps-convert e $k))))]
    [(? symbol?)
     `(,cont ,term)]))

(define (cps term)
  (cps-convert term '(lambda (ans) ans)))
