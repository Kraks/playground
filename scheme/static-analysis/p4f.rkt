#lang racket

;; P4F for A-Normal Form with integers and booleans

;; Reference: Pushdown Control-Flow Analysis for Free
;; Thomas Gilray, Steven Lyde, Michael D. Adams, Matthew Might, David Van Horn

(struct State (expr env store kaddr time) #:transparent)
(struct Clo (lam env) #:transparent)
(struct Kont (frame kaddr) #:transparent)
(struct Frame (var exp env) #:transparent)
(struct BAddr (var time) #:transparent)
(struct KAddr (expr time) #:transparent)
(struct KAddr-P4F (expr env tune) #:transparent)
(struct HaltK () #:transparent)

; Environment
(define mt-env (make-immutable-hash))
(define ext-env hash-set)
(define lookup-env hash-ref)

; Store
(define d-bot (set))
(define mt-store (make-immutable-hash))
(define (lookup-store store addr)
  (hash-ref store addr d-bot))
(define (update-store store addr vals)
  (hash-update store addr
               (λ (d) (set-union d vals))
               d-bot))

(define k (make-parameter 1))

(define (tick s)
  (take (cons (State-expr s) (State-time s)) (k)))

(define (atom? expr)
  (match expr
    [(? symbol?) #t]
    [(? number?) #t]
    [`(lambda (,args ...) ,body) #t]
    [else #f]))

; aeval : aexp env store -> set
(define (aeval aexpr env store)
  (match aexpr
    [(? number? x) (set x)]
    [(? symbol? x) (lookup-store store (lookup-env env x))]
    [`(lambda (,args ...) ,body)
     (set (Clo aexpr env))]
    [else (error 'aeval "Not an atomic expression")]))

(define (primop? op)
  (or (eq? op '+) (eq? op '-) (eq? op '*) (eq? op '==)))

(define (eval-prim op l r)
  (match op
    ['+ (list->set (flatten (for/list ([x l]) (for/list ([y r]) (+ x y)))))]
    ['- (list->set (flatten (for/list ([x l]) (for/list ([y r]) (- x y)))))]
    ['* (list->set (flatten (for/list ([x l]) (for/list ([y r]) (* x y)))))]
    ['== (list->set (flatten (for/list ([x l]) (for/list ([y r]) (eq? x y)))))]))

(define lam-args second)
(define lam-body third)

(define (alloc-bind var time)
  (BAddr var time))

(define (alloc-kont state target-expr target-env target-store time)
  (KAddr target-expr time))

(define (alloc-kont-p4f state target-expr target-env target-store time)
  (KAddr-P4F target-expr target-env time))

; step : state -> [state]
(define (step s)
  ;(displayln s)
  (define time* (tick s))
  (match s
    [(State `(,(? primop? op) ,e1 ,e2) env store kaddr time)
     (define v1 (aeval e1 env store))
     (define v2 (aeval e2 env store))
     (define result (eval-prim op v1 v2))
     (for/list ([n result])
       (State n env store kaddr time*))]
    [(State (? atom? x) env store kaddr time)
     (for/list ([k (lookup-store store kaddr)])
       (define k-env (Frame-env (Kont-frame k)))
       (define k-var (Frame-var (Kont-frame k)))
       (define k-exp (Frame-exp (Kont-frame k)))
       (define b-addr (alloc-bind k-var time*))
       (define new-env (ext-env k-env k-var b-addr))
       (define new-store (update-store store b-addr (aeval x env store)))
       (define new-kaddr (Kont-kaddr k))
       (State k-exp new-env new-store new-kaddr time*))]
    [(State `(let ([,var (lambda (,arg) ,body)]) ,e) env store kaddr time)
     (define b-addr (alloc-bind var time*))
     (define new-env (ext-env env var b-addr))
     (define new-store (update-store store b-addr (set (Clo `(lambda (,arg) ,body) env))))
     (list (State e new-env new-store kaddr time*))]
    [(State `(let ([,var (,f ,arg)]) ,e) env store kaddr time)
     (for/list ([clo (aeval f env store)])
       (define clo-env (Clo-env clo))
       (define arg-name (first (second (Clo-lam clo))))
       (define body (third (Clo-lam clo)))
       (define b-addr (alloc-bind arg-name time*))
       (define new-env (ext-env clo-env arg-name b-addr))
       (define new-store (update-store store b-addr (aeval arg env store)))
       (define k-addr (alloc-kont-p4f s body new-env new-store time*))
       (define new-new-store (update-store new-store k-addr
                                           (set (Kont (Frame var e env) kaddr))))
       (State body new-env new-new-store k-addr time*))]
    [s (list s)]))

(define (inject e)
  (State e mt-env mt-store (HaltK) '()))

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

;;

;(define prog '(let ([id ((lambda (x) x) (lambda (y) y))])
;                id))
;(aval prog)

;(define addone '(let ([four ((lambda (x) (+ x 1)) 3)])
;                four))
;(aval addone)


(define id '(let ([id (lambda (x) x)])
              (let ([one (id 1)])
                (let ([two (id 2)])
                  two))))
(aval id)

