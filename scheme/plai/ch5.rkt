#lang plai-typed

(define-type ArithS
  [numS (n : number)]
  [uminusS (e : ArithS)]
  [plusS (l : ArithS) (r : ArithS)]
  [bminusS (l : ArithS) (r : ArithS)]
  [multS (l : ArithS) (r : ArithS)])

(define-type FunDefC
  [fdC (name : symbol) (arg : symbol) (body : ExprC)])

(define-type ExprC
  [numC (n : number)]
  [idC (s : symbol)]
  [appC (fun : symbol) (arg : ExprC)]
  [plusC (l : ExprC) (r : ExprC)]
  [multC (l : ExprC) (r : ExprC)])

; parser from chapter 2
; parse : s-expression -> ArithS
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

; subst : ExprC * symbol * ExprC -> ExprC
(define (subst [what : ExprC] [for : symbol] [in : ExprC]): ExprC
  (type-case ExprC in
    [numC (n) in]
    [idC (s) (cond [(symbol=? s for) what]
                   [else in])]
    [appC (f a) (appC f (subst what for a))]
    [plusC (l r) (plusC (subst what for l)
                        (subst what for r))]
    [multC (l r) (plusC (subst what for l)
                        (subst what for r))]))

; get-fundef : symbol * (listof FunDefC) -> FunDefC
(define (get-fundef [n : symbol] [fds : (listof FunDefC)]) : FunDefC
  (cond [(empty? fds) (error 'get-fundef "reference to undefined function")]
        [(cons? fds) (cond
                       [(equal? n (fdC-name (first fds))) (first fds)]
                       [else (get-fundef n (rest fds))])]))

; lazy, or call-by-name
(define (interp [e : ExprC] [fds : (listof FunDefC)]) : number
  (type-case ExprC e
    [numC (n) n]
    [idC (_) (error 'interp "shouldn't get here")]
    [appC (func args) (local ([define fd (get-fundef func fds)])
                        (interp (subst args (fdC-arg fd) (fdC-body fd))
                                fds))]
    [plusC (l r) (+ (interp l fds) (interp r fds))]
    [multC (l r) (* (interp l fds) (interp r fds))]))

;; test
(fdC 'double 'x (plusC (idC 'x) (idC 'x)))
(fdC 'quardruple 'x (appC 'double (appC 'double (idC 'x))))
(fdC 'cons5 '_ (numC 5))

(test (interp (appC 'double (numC 10)) (list (fdC 'double 'x (plusC (idC 'x) (idC 'x))))) 20)

; eager interp, or call-by-value
(define (interp-cbv [e : ExprC] [fds : (listof FunDefC)]) : number
  (type-case ExprC e
    [numC (n) n]
    [idC (_) (error 'interp "shouldn't get here")]
    [appC (func args) (local ([define fd (get-fundef func fds)])
                        (interp-cbv (subst (numC (interp-cbv args fds))
                                           (fdC-arg fd)
                                           (fdC-body fd))
                                    fds))]
    [plusC (l r) (+ (interp-cbv l fds) (interp-cbv r fds))]
    [multC (l r) (* (interp-cbv l fds) (interp-cbv r fds))]))

(test (interp-cbv (appC 'double (plusC (numC 1) (numC 2))) (list (fdC 'double 'x (plusC (idC 'x) (idC 'x))))) 6)
