#lang racket

(require redex)

;; July 10

(define-language Λ
  (e ::=
     x
     (λ (x) e)
     (e e))
  (x := variable-not-otherwise-mentioned))
  ;#:binding-forms
  ;(λ (x) e #:refers-to x))

(define term1 (term (λ (x) y)))
(default-language Λ)
;(term (substitute ,term1 y x))

#| Exercise 6 |#

(define-extended-language Env Λ
  (e ::= .... natural)
  (env ::= ((x e) ...)))

(define-metafunction Env
  lookup : x env -> e or #false
  [(lookup x_0 ()) #f]
  [(lookup x_0 ((x_1 e_1) (x_2 e_2) ...)) e_1 (side-condition (eq? (term x_0) (term x_1)))]
  [(lookup x_0 ((x_1 e_1) (x_2 e_2) ...)) (lookup x_0 ((x_2 e_2) ...))])

(test-equal (redex-match? Env env (term ((a 3) (b 4)))) #true)
(test-equal (redex-match? Env env (term ())) #true)
(test-equal (term (lookup a ((a 3) (b 4)))) 3)
(test-equal (term (lookup b ((a 3) (b 4)))) 4)
(test-equal (term (lookup c ((a 3) (b 4)))) #false)

#| Exercise 7 |#

(define-metafunction Env
  [(let ((x_0 e_0)) e_1) ((λ (x_0) e_1) e_0)]
  [(let ((x_0 e_0) (x_1 e_1) ...) e_2)
   (term (let ((x_1 e_1) ...) ((λ (x_0) e_2) e_0)))])

(test-equal (term (let ((a 1)) a)) '((λ (a) a) 1))
(test-equal (term (let ((a (λ (x) x))) a)) '((λ (a) a) (λ (x) x)))
(test-equal (term (let ([id (λ (x) x)]) (id id))) '((λ (id) (id id)) (λ (x) x)))

#| Exercise 8 |#

(define-metafunction Env
  sd* : e -> e
  [(sd* e_0) (sd*-acc e_0 ())])

(define-metafunction Env
  sd*-acc : e (x ...) -> e
  [(sd*-acc x (x_1 ... x x_2 ...))
   (sd ,(length (term (x_1 ...))))]
  [(sd*-acc x any) x]
  [(sd*-acc (λ (x_0) e_1) (x_1 ...))
   (λ (x_0) (sd*-acc e_1 (x_0 x_1 ...)))]
  [(sd*-acc (e_1 e_2) (x ...))
   ((sd*-acc e_1 (x ...)) (sd*-acc e_2 (x ...)))])

(test-equal (term (sd* (λ (x) x))) (term (λ (x) (sd 0))))
(test-equal (term (sd* (λ (x) (λ (y) (y x)))))
            (term (λ (x) (λ (y) ((sd 0) (sd 1))))))

(define-extended-language Lambda-calculus Λ
  (C ::=
     hole
     (λ (x) C)
     (C e)
     (e C)))

(define ->name
  (reduction-relation
   Lambda-calculus
   #:domain e
   (--> (in-hole C ((λ (x) e_1) e_2))
        (in-hole C (substitute e_1 x e_2))
        beta-name)))

;(apply-reduction-relation ->name (term ((λ (x) z) x)))

(define ->value
  (reduction-relation
   Lambda-calculus
   #:domain e
   (--> (in-hole C ((λ (x) e_1) (λ (x_y) e_2)))
        (in-hole C (substitute e_1 x (λ (x_y) e_2)))
        beta-value)))

(define e3
  (term
   ((λ (x) (λ (y) x))
    ((λ (x) x) z))))
 
;(traces ->name e3)

;; Curry-Feys Leftmost-outermost redex

#|
 referential transparent
 referential transparent position
   holes in context

  metafunction
    meta-interpreter (1972)
|#

(define-language PCF
  (e :=
     x
     (lambda (x) e)
     (e e)
     tt
     ff
     (if e e e)
     n
     (e + e))
  (n ::= natural)
  (x := variable-not-otherwise-mentioned)
  #:binding-forms
  (λ (x) e #:refers-to x))

(define-extended-language PCF-eval PCF
  (E-name ::=
          hole
          (E-name e)
          (if E-name e e)
          (E-name + e)
          (v + E-name))
  (v ::=
     n
     tt
     ff
     (lambda (x) e)))

(define PCF->name
  (reduction-relation
   PCF-eval
   #:domain e
   (--> (in-hole E-name ((lambda (x) e_1) e_2))
        (in-hole E-name (substitute e_1 x e_2))
        beta-name)
   (--> (in-hole E-name (if tt e_1 e_2))
        (in-hole E-name e_1)
        if-tt)
   (--> (in-hole E-name (if ff e_1 e_2))
        (in-hole E-name e_2)
        if-ff)
   (--> (in-hole E-name (n_1 + n_2))
        (in-hole E-name ,(+ (term n_1) (term n_2)))
        plus)))

;(apply-reduction-relation PCF->name (term (3 + 4)))
;(apply-reduction-relation* PCF->name (term ((lambda (x) (x + 1)) 3)))

#| Exercise 1 |#

(define-extended-language PCF-value PCF
  (e ::= .... (e - e))
  (E-value ::=
           hole
           (E-value e)
           (v E-value)
           (if E-value e e)
           (E-value + e)
           (v + E-value)
           (E-value - e)
           (v - E-value))
  (v ::=
     n
     tt
     ff
     (lambda (x) e)))

(define PCF->value
  (reduction-relation
   PCF-value
   #:domain e
   (--> (in-hole E-value ((lambda (x) e_1) v_1))
        (in-hole E-value (substitute e_1 x v_1))
        beta-value)
   (--> (in-hole E-value (if tt e_1 e_2))
        (in-hole E-value e_1)
        if-tt)
   (--> (in-hole E-value (if ff e_1 e_2))
        (in-hole E-value e_2)
        if-ff)
   (--> (in-hole E-value (n_1 + n_2))
        (in-hole E-value (plus n_1 n_2)))
   (--> (in-hole E-value (n_1 - n_2))
        (in-hole E-value (minus n_1 n_2)))
   ))

#| Exercise 4 & 5 |#

(define-metafunction PCF-value
  plus : n n -> n
  [(plus n_1 n_2) ,(+ (term n_1) (term n_2))])

(define-metafunction PCF-value
  minus : n n -> n
  [(minus n_1 n_2) ,(- (term n_1) (term n_2))
                   (side-condition (> (term n_1) (term n_2)))]
  [(minus _ _) 0])
                                
(test-equal (apply-reduction-relation PCF->value (term (2 - 1))) '(1))
(test-equal (apply-reduction-relation PCF->value (term (2 - 3))) '(0))

(test-equal (apply-reduction-relation PCF->value
                                      (term ((lambda (x) (x + 1)) (1 + 1))))
            '(((lambda (x) (x + 1)) 2)))
(test-equal (apply-reduction-relation PCF->value
                                      (term (((lambda (x) (lambda (y) (x + y))) (3 + 4)) (4 + 3))))
            '((((lambda (x) (lambda (y) (x + y))) 7) (4 + 3))))

(test-equal (apply-reduction-relation* PCF->value
                                       (term (((lambda (x) (lambda (y) (x + y))) (3 + 4)) (4 + 3))))
            '(14))

#| Exercise 2 |#

(define-extended-language PCF-value/str PCF-value
  (e ::=
     ....
     str
     (e ++ e))
  (str ::= string)
  (E-value ::=
           ....
           (E-value ++ e)
           (v ++ E-value))
  (v ::= .... str))

(define PCF->value/str
  (extend-reduction-relation
   PCF->value
   PCF-value/str
   #:domain e
   (--> (in-hole E-value (str_1 ++ str_2))
        (in-hole E-value ,(string-append (term str_1) (term str_2))))))

(test-equal (apply-reduction-relation PCF->value/str (term ("a" ++ "b")))
            '("ab"))
(test-equal (apply-reduction-relation* PCF->value/str (term ((lambda (name) (("Hello" ++ " ") ++ name)) "Racket")))
            '("Hello Racket"))

#| Exercise 3 |#

(define-extended-language PCF-value/err PCF-value
  (e ::= .... (err string))
  (not-num ::= tt ff (lambda (x) e) (err string))
  (v ::= .... (err string)))
         
(define PCF->value/err
  (extend-reduction-relation
   PCF->value
   PCF-value/err
   #:domain e
   (--> (in-hole E-value (not-num + e_1))
        (err "not a number"))
   (--> (in-hole E-value (v_1 + not-num))
        (err "not a number"))
   (--> (in-hole E-value ((err string_1) e_1))
        (err string_1))
   (--> (in-hole E-value (v_1 (err string_1)))
        (err string_1))))

(test-equal (apply-reduction-relation PCF->value/err (term (1 + tt)))
            '((err "not a number")))
(test-equal (apply-reduction-relation PCF->value/err (term (1 + ((lambda (x) x) + 3))))
            '((err "not a number")))
(test-equal (apply-reduction-relation* PCF->value/err (term ((lambda (x) (x + ((lambda (y) y) + 3))) 3)))
            '((err "not a number")))



#|
lang designer does not have a semantics model when they design the language.
modeling existing language, need to invent tricks
every runtime states can be written down by syntax
|#

