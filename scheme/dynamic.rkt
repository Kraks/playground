#lang typed/racket

; This is dynamically scope interpreter.
; That means the environment accumulates bindings as the program executes. 
; As a result, whether an identifier is even bound depends on the history 
; of program execution.

(define-type Expr
  (U Void
     Number 
     String 
     Boolean 
     Id
     App
     Plus
     Mult
     Fun
     Begin))

(struct: Id ([s : Symbol]))
(struct: App ([fun : (U Symbol Fun)] [arg : Expr]))
(struct: Plus ([l : Expr] [r : Expr]))
(struct: Mult ([l : Expr] [r : Expr]))
(struct: Fun ([arg : Symbol] [body : Expr]))
(struct: Begin ([exprs : (Listof Expr)]))

(struct: Binding ([name : Symbol] [val : Expr]))

(define-type-alias Env (Listof Binding))
(define extend-env cons)

(: Any? (-> Any Boolean))
(define (Any? anything) #t)

(: lookup (-> Symbol Env Expr))
(define lookup
  (lambda (s env)
    (cond
      [(empty? env) (error 'lookup "name not found")]
      [else (cond [(symbol=? s (Binding-name (first env)))
                   (Binding-val (first env))]
                  [else (lookup s (rest env))])])))

(: dyn-interp (-> Expr Env Expr))
(define dyn-interp
  (lambda (expr env)
    (match expr
      [(? number? expr) expr]
      [(? string? expr) expr]
      [(? boolean? expr) expr]
      [(Id x) (lookup x env)]
      [(Plus x y)
       (cond [(and (number? x) (number? y)) (+ x y)]
             [else (dyn-interp (Plus (dyn-interp x env)
                                     (dyn-interp y env)) env)])]
      [(Mult x y)
       (cond [(and (number? x) (number? y)) (* x y)]
             [else (dyn-interp (Mult (dyn-interp x env)
                                     (dyn-interp y env)) env)])]
      [(App fun arg)
       (cond [(symbol? fun)
              (let ([fn (lookup fun env)])
                (cond [(Fun? fn) (dyn-interp (App fn arg) env)]
                      [else (error 'dyn-interp 
                                   (string-append "can not apply " (symbol->string fun)))]))]
             [(Fun? fun)
              (dyn-interp (Fun-body fun)
                          (extend-env (Binding (Fun-arg fun) (dyn-interp arg env)) env))])]
      [(Begin exprs)
       (foldl (lambda ([x : Expr] [y : Expr])
                (dyn-interp x env)) (void) exprs)]
      [(? Any? x) x])))

(define t1 (Plus (Id 'x) (Id 'y)))
(define t2 (Mult 3 t1))
(define add1 (Fun 'x (Plus (Id 'x) 1)))
(define env0
  (list (Binding 'x 1)
        (Binding 'y 2)
        (Binding 'add1 add1)))

(define f1 (App (Fun 'x (App (Fun 'y (Plus (Id 'x) (Id 'y))) 3)) 4))
(dyn-interp f1 env0)

(define b1
  (Begin (list
          (App 'add1 3)
          (App 'add1 4))))