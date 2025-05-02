#lang racket

(require redex)

(provide (all-defined-out))

;; ---------------------------------------------------------------------------------------------------
;; syntax

(define-language basic-syntax
  (p ::= (prog f ... e))
  (f ::= (defun (x x) e))
  (e ::=
     ;; booleans
     b
     (if e e e)
     ;; numbers
     n
     (zero? e)
     (+ e e)
     ;; strings
     s
     (empty? e)
     (++ e e)
     ;; functions & let
     (function x)
     (e e)
     x
     (let ((x e)) e))
  (x ::= variable-not-otherwise-mentioned)
  (b ::= true false)
  (n ::= number)
  (s ::= string)
  (v ::=
     b
     n
     s
     (function x))
  #:binding-forms
  (let ((x e_1)) e_2 #:refers-to x))
  

;; ---------------------------------------------------------------------------------------------------
;; evaluation

(define-extended-language basic-lang basic-syntax
  (P ::= (prog f ... E))
  (E ::=
     hole
     ;; booleans
     (if E e e)
     ;; numbers
     (zero? E)
     (+ E e)
     (+ v E)
     ;; strings
     (empty? E)
     (++ E e)
     (++ v E)
     ;; functions & let
     (E e)
     (v E)
     (let ((x E)) e)))

(define basic->
  (reduction-relation basic-lang
   ;; booleans
   (--> (in-hole P (if true e_then e_else))
        (in-hole P e_then)
        e-if-true)
   (--> (in-hole P (if false e_then e_else))
        (in-hole P e_else)
        e-if-false)
   ;; numbers
   (--> (in-hole P (zero? 0))
        (in-hole P true)
        e-zero-yes)
   (--> (in-hole P (zero? n))
        (in-hole P false)
        (side-condition (not (equal? (term n) 0)))
        e-zero-no)
   (--> (in-hole P (+ n_1 n_2))
        (in-hole P ,(+ (term n_1) (term n_2)))
        e-plus)
   ;; strings
   (--> (in-hole P (empty? ""))
        (in-hole P true)
        e-empty-yes)
   (--> (in-hole P (empty? s))
        (in-hole P false)
        (side-condition (not (equal? (term s) "")))
        e-empty-no)
   (--> (in-hole P (++ s_1 s_2))
        (in-hole P ,(string-append (term s_1) (term s_2)))
        e-append)
   ;; termination
   (--> (prog f ... v)
        v
        e-halt)
   ;; id
   (--> (prog f_1 ... (defun (x_fun x_param) e_body) f_2 ...
              (in-hole E x_fun))
        (prog f_1 ... (defun (x_fun x_param) e_body) f_2 ...
              (in-hole E (function x_fun)))
        e-id)
   ;; let
   (--> (in-hole P (let ((x v)) e))
        (in-hole P (substitute e x v))
        e-let)
   ;; apply
   (--> (prog f_1 ... (defun (x_fun x_param) e_body) f_2 ...
              (in-hole E ((function x_fun) v_arg)))
        (prog f_1 ... (defun (x_fun x_param) e_body) f_2 ...
              (in-hole E (substitute e_body x_param v_arg)))
        e-apply)))

(define-extended-language record-syntax basic-lang
  (e ::= ....
     (record (s e) ...)
     (@ e e))
  (v ::= ....
     (record (s v) ...)))

(define-extended-language record-lang-1 record-syntax
  (E ::= ....
     (record (s v) ... (s E) (s e) ...)
     (@ E e)))

(define-metafunction record-lang-1
  lookup : (record (s v) ...) s -> v or stuck
  [(lookup (record (s_0 v_0) ... (s_1 v_1) (s_2 v_2) ...) s_1) v_1]
  [(lookup (record (s_0 v_0) ...) s) stuck])

(test-equal (term (lookup (record ("a" 1)) "a")) 1)
(test-equal (term (lookup (record ("a" 1) ("b" 2)) "b")) 2)
(test-equal (term (lookup (record ("a" 1) ("b" 2) ("c" 3)) "b")) 2)
(test-equal (term (lookup (record ("a" 1)) "c")) (term stuck))

(define record->1
  (extend-reduction-relation basic-> record-lang-1
   (--> (in-hole P (@ (record (s v) ...) s_1))
        (in-hole P (lookup (record (s v) ...) s_1))
        e-at)))

(test-equal (apply-reduction-relation record->1 (term (prog (@ (record ("a" 1)) "a"))))
            '((prog 1)))
(test-equal (apply-reduction-relation record->1 (term (prog (@ (record ("a" 1) ("b" 2)) "b"))))
            '((prog 2)))
(test-equal (apply-reduction-relation record->1 (term (prog (@ (record ("a" 1) ("b" 2)) "c"))))
            '((prog stuck)))

(traces record->1 (term (prog (defun (f rec) (@ rec "b")) (f (record ("a" 1) ("b" 2))))))