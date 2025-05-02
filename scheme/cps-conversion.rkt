#lang racket

#|
The input language:
<expr> := (lambda (<var>) <expr>)
        | <var>
        | (<expr> <expr>)

The CPS form:
<aexp> := (lambda (<var>*) <cexp>)
        | <var>

<cexp> := (<aexp> <aexp>*)

The atomic expressions always produce a value and never cause side effects.
The complex expressions may not terminate, and may have side effects.
|#


;; Naive transformation

; M converts an atomic value (a variable or lambda term) into an atomic CPS value.
; M : expr -> aexp
(define (M expr)
  (match expr
    [`(λ (,var) ,expr)
      (define $k (gensym '$k))
      `(λ (,var ,$k) ,(T expr $k))]
    [(? symbol?) expr]))

; T takes an expression and a syntactic continuation, and applies the continuation
; to a CPS-converted version of the expression.
; T : expr aexp -> cexp
(define (T expr cont)
  (match expr
    [(? symbol?) `(,cont ,(M expr))]
    [`(λ . ,_) `(,cont ,(M expr))]
    [`(,f ,e)
     (define $f (gensym '$f))
     (define $e (gensym '$e))
     (T f `(λ (,$f)
             ,(T e `(λ (,$e)
                      (,$f ,$e ,cont)))))]))

; example
(T '(f g) 'halt)


;; The Higher-order transformation
