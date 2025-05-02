#lang racket
;; CESK Machine for ANF

; update : (a -> b) a b -> (a -> b)
(define (update f x y)
  (λ (x*)
    (if (equal? x x*)
        y
        (f x*))))

; Assertion:
; if x != x'
; then (f x) == ((update f x' y) x)

; Assertion:
; ((update f x y) x) == y

; update* : (a -> b) [a] [b] -> (a -> b)
(define (update* f xs ys)
  (match* (xs ys)
    [['() '()] f]
    [[(cons x xs*) (cons y ys*)]
     (update* (update f x y) xs* ys*)]))

; atom? : exp -> boolean?
(define (atom? exp)
  (match exp
    [`(λ ,_ ,_) #t]
    [(? symbol?) #t]
    [(? boolean?) #t]
    [(? integer?) #t]
    [(cons (? prim?) _) #t]
    [else #f]))

; prim? : symbol? -> boolean?
(define (prim? exp)
  (case exp
    [(+ - * = void) #t]
    [else #f]))

; CESK Machine state
(struct state { control
                environment
                store
                continuation }
        #:transparent)

; ρ : env = symbol -> addr

; σ : store = addr -> value

; value = integer + boolean + clo + cont

; clo ::= (clo <lam> <env>)

; κ : kont ::= (letk <var> <exp> <env> <kont>)
;           |  halt

; cont ::= (cont <kont>)

; addr = a set of unique addresses;
;        for this machine, symbols work;
;        gensym can create fresh addresses

; apply-kont : kont value store -> (state + answer)
(define (apply-kont k value s)
  (match k
    ; apply the halt continuation
    ['halt `(answer ,value ,s)]
    ; resume execution
    [`(letk ,var ,exp ,env ,kont)
     (define a* (gensym 'a)) ; fresh address
     (state exp (update env var a*) (update s a* value) kont)]))

; prim->proc: symbol? -> procedure?
(define (prim->proc prim)
  (match prim
    ['+ +]
    ['- -]
    ['* *]
    ['= =]
    ['void void]))

; eval-atom : aexp env store -> value
(define (eval-atom aexp env store)
  (match aexp
    [(? symbol?) (store (env aexp))]
    [(? boolean?) aexp]
    [(? integer?) aexp]
    [(cons (and prim (? prim?)) rest)
     (let ([args (map (eval-atom/curry env store) rest)])
       (apply (prim->proc prim) args))]
    [`(λ ,_ ,_)
     `(clo ,aexp ,env)]
    [else (error (format "unknown atom ~a" aexp))]))

; eval-atom/curry : env store -> aexp -> value
(define (eval-atom/curry env store)
  (λ (atom) (eval-atom atom env store)))

; env0 is the initial (empty) environment
(define env0 (λ (v) (error (format "unbound variable ~a" v))))

; store0 is the initial (empty) store
(define store0 (λ (addr) (error (format "unbound address ~a" addr))))

; inject : exp -> state
(define (inject exp)
  (state exp env0 store0 'halt))

; apply-proc : value [value] store kont -> (state + answer)
(define (apply-proc proc args store kont)
  (match proc
    ; apply a closure
    [`(clo (λ ,vars ,body) ,env)
     ; allocate fresh addresses
     (define addrs (map gensym vars))
     ; update the environment
     (define env* (update* env vars addrs))
     ; update the store
     (define store* (update* store addrs args))
     (state body env* store* kont)]
    
    ; apply a continuation
    [`(cont ,kont*)
     (apply-kont kont* (car args) store)]))

; step : state -> (state + answer)
(define (step s)
  (match s
    ; return
    [(state (and atom (? atom?)) env store kont)
     ; evaluate the return value
     (define return-value (eval-atom atom env store))
     (apply-kont kont return-value store)]
    
    ; conditional evaluation
    [(state `(if ,cond ,cons ,alt) env store kont)
     (if (eval-atom cond env store)
         (state cons env store kont)
         (state alt env store kont))]
    
    ; call with current contination
    [(state `(call.cc ,f) env store kont)
     ; lookup the procedure to call
     (define proc (eval-atom f env store))
     ;capture the current contunation
     (define cc `(cont ,kont))
     (apply-proc proc (list cc) store kont)]
    
    ; mutation
    [(state `(set! ,var ,aexp) env store kont)
     (define value (eval-atom aexp env store))
     (define store* (update store (env var) value))
     (apply-kont kont (void) store*)]
    
    ; letrec
    [(state `(letrec ([,vars ,aexps] ...) ,body) env store kont)
     ; allocate fresh addresses
     (define addrs (map gensym vars))
     ; update the environment
     (define env* (update* env vars addrs))
     ; evaluate the expressions with the *new* env
     (define values (map (eval-atom/curry env* store) aexps))
     ; update the store
     (define store* (update* store addrs values))
     (state body env* store* kont)]
    
    ; let-binding
    [(state `(let ([,var ,exp]) ,body) env store kont)
     (state exp env store `(letk ,var ,body ,env ,kont))]
    
    ; function application
    [(state `(,func . ,es) env store kont)
     ; evaluate the procedure
     (define proc (eval-atom func env store))
     ; evaluate the arguments
     (define args (map (λ (x) (eval-atom x env store)) es))
     (apply-proc proc args store kont)]))

; step* : state -> answer
(define count 0)
(define (step* s)
  (if (state? s)
      (begin
        ;(displayln s)
        (set! count (+ 1 count))
        (step* (step s)))
      s))

; run : exp -> answer
(define (run exp)
  (define s0 (inject exp))
  (step* s0))

; example, fact
(define fact-prog
  '(letrec ([f (λ (n) (if (= n 0)
                          1
                          (let ([n-1! (f (- n 1))])
                            (* n n-1!))))])
     (f 5)))
;(run fact-prog)

(define fib-prog
  '(letrec ([f (λ (n) (if (= n 0) 0
                          (if (= n 1) 1
                              (let ([n-1 (f (- n 1))])
                                (let ([n-2 (f (- n 2))])
                                  (+ n-1 n-2))))))])
     (f 20)))

;(run fib-prog)
(display count)
