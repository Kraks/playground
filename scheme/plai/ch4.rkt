#lang plai-typed

(define-type ArithC
  [numC (n : number)]
  [plusC (l : ArithC) (r : ArithC)]
  [multC (l : ArithC) (r : ArithC)])

(define-type ArithS
  [numS (n : number)]
  [uminusS (e : ArithS)]
  [plusS (l : ArithS) (r : ArithS)]
  [bminusS (l : ArithS) (r : ArithS)]
  [multS (l : ArithS) (r : ArithS)])

; parser from chapter 2
(define (parse [s : s-expression]) : ArithS
  (cond
    [(s-exp-number? s) (numS (s-exp->number s))]
    [(s-exp-list? s)
     (let ([sl (s-exp->list s)])
       (case (s-exp->symbol (first sl))
         [(+) (plusS (parse (second sl)) (parse (third sl)))]
         [(*) (multS (parse (second sl)) (parse (third sl)))]
         [(-) (cond ((eq? (length sl) 2) (uminusS (parse (second sl))))
                    (else (bminusS (parse (second sl)) (parse (third sl)))))]
         [else (error 'parse "invalid list input")]))]
    [else (error 'parse "invalid input")]))

(define (desugar [as : ArithS]) : ArithC
  (type-case ArithS as
    [numS (n) (numC n)]
    [plusS (l r) (plusC (desugar l) (desugar r))]
    [multS (l r) (multC (desugar l) (desugar r))]
    ;[uminusS (e) (desugar (bminusS (numS 0) e))]
    [uminusS (e) (multC (numC -1) (desugar e))] ;another way to desugar -n
    [bminusS (l r) (plusC (desugar l) (multC (numC -1) (desugar r)))]))

(define (interp [a : ArithC]) : number
  (type-case ArithC a
    [numC (n) n]
    [plusC (l r) (+ (interp l) (interp r))]
    [multC (l r) (* (interp l) (interp r))]))

(test (interp (desugar (parse '(+ (* 1 2) (+ 2 3))))) 7)
(test (interp (desugar (parse '(- (+ 1 2))))) -3)
(test (interp (desugar (parse '(- (- (* 3 3)))))) 9)
