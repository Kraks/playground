#lang racket

;; ΓCFA implementation for CPS
;; Reference: Improving Flow Analyses via ΓCFA, Matthew Might and Olin Shivers

(struct Clo (lam env) #:transparent)
(struct BAddr (var time) #:transparent)
(struct Eval (call env store count time) #:transparent)
(struct Apply (proc ds store count time) #:transparent)

(define lam-args second)
(define lam-body third)

(define mt-env (make-immutable-hash))
(define ext-env hash-set)
(define lookup-env hash-ref)

(define d-bot (set))
(define mt-store (make-immutable-hash))
(define (lookup-store store addr)
  (hash-ref store addr d-bot))
(define (update-store store addr vals)
  (hash-update store addr
               (λ (d) (set-union d vals))
               d-bot))

(define mt-mu (make-immutable-hash))
(define (lookup-mu mu addr)
  (hash-ref mu addr 0))
(define (add-mu mu addr v)
  (hash-update mu addr
               (λ (oldv) (match* (oldv v)
                           [(0 1) 1]
                           [(0 inf) 'inf]
                           [(1 1) 'inf]
                           [(1 inf) 'inf]
                           [(inf _) 'inf]))
               0))
(define (rebuild-mu mu reachable-binds)
  mu)

(define k (make-parameter 0))

(define (tick s) '())
#|
  (define state-expr first)
  (define state-time fifth)
  (take (cons (state-expr s) (state-time s)) (k)))
|#

(define (A v env store)
  (match v
    [(? number?) (set v)]
    [(? symbol?) (lookup-store store (lookup-env env v))]
    [`(lambda (,args ...) ,body)
     (set (Clo `(lambda (,@args) ,body) env))]
    [else (error 'A "not a primitive expr")]))

(define (primop? op)
  (or (eq? op '+) (eq? op '-) (eq? op '*) (eq? op '==)))

(define (eval-prim op l r)
  (match op
    ['+ (list->set (flatten (for/list ([x l]) (for/list ([y r]) (+ x y)))))]
    ['- (list->set (flatten (for/list ([x l]) (for/list ([y r]) (- x y)))))]
    ['* (list->set (flatten (for/list ([x l]) (for/list ([y r]) (* x y)))))]))

(define (step s)
  (define time* (tick s))
  (match s
    [(Eval (? symbol? x) env store mu time)
     (for/list ([v (A x env store)])
       (Eval v env store mu time*))]
    [(Eval `(,(? primop? op) ,args ...) env store mu time)
     (define ds (map (λ (arg) (A arg env store)) args))
     (define vs (take ds 2))
     (define k (last args))
     (define anss (eval-prim op (first vs) (second vs)))
     (for/list ([ans anss])
       (Eval `(,k ,ans) env store mu time*))]
    [(Eval `(,f ,args ...) env store mu time)
     (define ds (map (λ (arg) (A arg env store)) args))
     (for/list ([proc (A f env store)])
       (Apply proc ds store mu time*))]
    [(Apply (Clo lam env) ds store mu time)
     (define args (lam-args lam))
     (define body (lam-body lam))
     (define addrs (map (λ (v) (BAddr v time*)) args))
     (define new-env (for/fold ([env env])
                               ([addr addrs]
                                [arg args])
                       (ext-env env arg addr)))
     (define new-store (for/fold ([store store])
                                 ([addr addrs]
                                  [d ds])
                         (update-store store addr d)))
     (define new-mu (for/fold ([mu mu])
                              ([addr addrs])
                      (add-mu mu addr 1)))
     (list (Eval body new-env new-store new-mu time*))]
    [s (list s)]))

(define (inject e)
  (Eval e mt-env mt-store mt-mu '()))

(define (explore f init)
  (search f (set) (list init) 0 (list)))

(define (search f seen todo id result)
  (cond [(empty? todo) result]
        [(set-member? seen (first todo))
         (search f seen (rest todo) id result)]
        [else (search f (set-add seen (first todo))
                      (append (f (first todo)) (rest todo))
                      (add1 id)
                      (cons (cons id (first todo)) result))]))

(define (aval e) (explore step (inject e)))

;; Test programs
(define p1 '((lambda (id k) (k id))
             (lambda (x) x)
             (lambda (x) x)))
;(aval p1)

(define five '(+ 3 2 (lambda (x) x)))
;(aval five)

; (* (+ 1 2) (- 5 3))
(define add '(+ 1 2 (lambda (x) (- 5 3 (lambda (y) (* x y (lambda (k) k)))))))
;(aval add)

;; Abstract Garbage Collection

(define (free e)
  (match e
    [(? number?) (set)]
    [(? symbol?) (set e)]
    [`(,(? primop?) ,l ,r ,k)
     (set-union (free l) (free r) (free k))]
    [`(lambda ,args ,body)
     (set-subtract (free body) (apply set args))]
    [`(,f ,args ...)
     (apply set-union (map free `(,f . ,args)))]))

(define (touchable e)
  (match e
    [(Clo lam env)
     (for/set ([v (free lam)])
       (lookup-env env v))]
    [(? set? s)
     (apply set-union (set-map s touchable))]
    [(Eval e env store mu time)
     (for/set ([v (free e)])
       (lookup-env env v))]
    [(Apply proc ds store mu time)
     (apply set-union (set-map (list->set `(,proc ,@ds)) touchable))]
    [else (set)]))

;; TODO
(define (reachable s)
  (define store
    (cond [(Eval? s) (Eval-store s)]
          [(Apply? s) (Apply-store s)]))
  (define (search todo done)
    (cond [(set-empty? todo) done]
          [(set-member? done (set-first todo))
           (search (set-rest todo) done)]
          [else (search (set-union (apply set-union (map touchable
                                                         (lookup-store store (set-first todo))))
                                   (set-rest todo))
                        (set-add done (set-first todo)))]))
  (search (touchable s) (set)))

