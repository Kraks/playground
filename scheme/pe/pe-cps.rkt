#lang racket

;; Online Partial Evaluator
; The code is adapted from paper Tutorial Notes on Partial Evaluation,
; which originally written in Haskell.

;; The Language is first-order, which means functions cannot be used as values.
; var  ::= symbol
; fdef ::= ((var ...) expr)
; expr ::= number | boolean
;        | symbol
;        | (primop expr expr)
;        | (if expr expr expr)
;        | (var expr ...)
; primop ::= + | - | * | ==

(struct FDef (args body) #:transparent)
(struct None () #:transparent)

(define (lookup key env)
  (cond [(null? env) (None)]
        [(equal? key (first (first env))) (second (first env))]
        [else (lookup key (rest env))]))

(define (update key val env)
  (cond [(null? env) (list key val)]
        [(equal? key (first (first env)))
         (cons (list key val) (rest env))]
        [else (cons (first env) (update key val (rest env)))]))

(define (op? op)
  (or (symbol=? op '==) (symbol=? op '+)
      (symbol=? op '-)  (symbol=? op '*)))

(define (is-value? v) (or (number? v) (boolean? v)))

(define (aexp op l r)
  (match op
    ['+ (+ l r)]
    ['* (* l r)]
    ['- (- l r)]
    ['== (eq? l r)]))

(define (new-function-name old-name args)
  (string->symbol (string-append (symbol->string old-name)
                                 (number->string (equal-hash-code args)))))

(define (peval fdefs expr)
  (define (pe expr env fdefs cont)
    (match expr
      [(or (? number?) (? boolean?)) (cont expr fdefs)]
      [(? symbol?)
       (define val (lookup expr env))
       (cont (if (None? val) expr val) fdefs)]
      [`(,(? op? op) ,l ,r)
       (pe l env fdefs
           (λ (lv fdefs)
             (pe r env fdefs
                 (λ (rv fdefs)
                   (cont (if (and (is-value? lv) (is-value? rv))
                             (aexp op lv rv)
                             `(,op ,lv ,rv))
                         fdefs)))))]
      [`(if ,cnd ,thn ,els)
       (pe cnd env fdefs
           (λ (cnd-v fdefs)
             (if (is-value? cnd-v)
                 (if cnd-v
                     (pe thn env fdefs cont)
                     (pe els env fdefs cont))
                 (pe thn env fdefs
                     (λ (thn-v fdefs)
                       (pe els env fdefs
                           (λ (els-v fdefs)
                             (cont `(if ,cnd ,thn-v ,els-v) fdefs))))))))]
      [`(,fname ,args ...)
       (define (pe-args lst vs fdefs cont)
         (cond [(empty? lst) (cont (reverse vs) fdefs)]
               [else (pe (first lst) env fdefs
                         (λ (v fdefs) (pe-args (rest lst) (cons v vs) fdefs cont)))]))
       (pe-args args '() fdefs
                (λ (args-v fdefs)
                  (define fun (lookup fname fdefs))
                  (define new-env (map list (FDef-args fun) args-v))
                  (define-values (statics dyns) (partition (compose is-value? second) new-env))
                  (if (empty? dyns)
                      (pe (FDef-body fun) statics fdefs cont)
                      (let ([new-fname (new-function-name fname statics)])
                        (if (None? (lookup new-fname fdefs))
                            (pe (FDef-body fun) statics (cons `(,new-fname 'placeholder) fdefs)
                                (λ (fun-v fdefs)
                                  (cont `(,new-fname ,@(map second dyns))
                                        (update new-fname (FDef (map first dyns) fun-v) fdefs))))
                            (cont `(,new-fname ,@(map second dyns)) fdefs))))))]))
  (pe expr '() fdefs (λ (ans fdefs) (list fdefs ans))))

(module* test #f
  (require rackunit)
  (define mt-fdefs '())
  (define add (list 'add (FDef '(x y) '(+ x y))))
  (define exp (list 'exp (FDef '(x n) '(if (== n 0) 1
                                           (* x (exp x (- n 1)))))))
  
  (check-equal? (peval mt-fdefs 3) '(() 3))
  (check-equal? (peval mt-fdefs #t) '(() #t))
  (check-equal? (peval mt-fdefs #f) '(() #f))
  (check-equal? (peval mt-fdefs '(+ 3 4)) '(() 7))
  (check-equal? (peval mt-fdefs '(* 3 4)) '(() 12))
  (check-equal? (peval mt-fdefs '(- 3 4)) '(() -1))
  (check-equal? (peval mt-fdefs '(== 3 4)) '(() #f))
  (check-equal? (peval mt-fdefs '(== a 4)) '(() (== a 4)))
  (check-equal? (peval mt-fdefs '(if #f a 3)) '(() 3))
  (check-equal? (peval mt-fdefs '(if #t a 3)) '(() a))
  (check-equal? (peval mt-fdefs '(if b a 3)) '(() (if b a 3)))
  (check-equal? (second (peval (list add) '(add 1 2)))
                3)
  
  (check-equal? (peval (list add) '(add 1 a))
                (list
                 (list
                  (list 'add467865875966180528 (FDef '(y) '(+ 1 y)))
                  (list 'add (FDef '(x y) '(+ x y))))
                 '(add467865875966180528 a)))
  
  (check-equal? (peval (list exp) '(exp x 3))
                (list
                 (list
                  (list 'exp468162305551269500 (FDef '(x) 1))
                  (list 'exp468162502326355551 (FDef '(x) '(* x (exp468162305551269500 x))))
                  (list 'exp468162501268068607 (FDef '(x) '(* x (exp468162502326355551 x))))
                  (list 'exp468162500416328378 (FDef '(x) '(* x (exp468162501268068607 x))))
                  (list 'exp (FDef '(x n) '(if (== n 0) 1 (* x (exp x (- n 1)))))))
                 '(exp468162500416328378 x)))
  
  (check-equal? (peval (list exp) '(exp 2 n))
                (list
                 (list
                  (list 'exp467865866941575679 (FDef '(n) '(if (== n 0) 1 (* 2 (exp467865866941575679 (- n 1))))))
                  (list 'exp (FDef '(x n) '(if (== n 0) 1 (* x (exp x (- n 1)))))))
                 '(exp467865866941575679 n))))
