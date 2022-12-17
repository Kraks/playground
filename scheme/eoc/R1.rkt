#lang racket

(require rackunit)
(require racket/fixnum)
(require racket/list
         (rename-in racket/list [flatten flatten/list]))

#| R1 Syntax
exp ::= int | (read) | (- exp) | (+ exp exp)
      | var | (let ([var exp]) exp)
R1  ::= (program exp)
|#

;; Interpreter

(define (lookup x env)
  (cond [(empty? env) (error 'lookup "unbound variable" x)]
        [(equal? (car (first env)) x)
         (cdr (first env))]
        [else (lookup x (rest env))]))

(define (interp-R1 env)
  (λ (e)
    (define recur (interp-R1 env))
    (match e
      [(? symbol?) (lookup e env)]
      [(? fixnum?) e]
      [`(let ([,x ,(app recur v)]) ,body)
       (define new-env (cons (cons x v) env))
       ((interp-R1 new-env) body)]
      [`(read)
       (define r (read))
       (cond [(fixnum? r) r]
             [else (error 'interp-R1 "expected an integer" r)])]
      [`(- ,(app recur v))
       (fx- 0 v)]
      [`(+ ,(app recur v1) ,(app recur v2))
       (fx+ v1 v2)]
      [`(program ,e)
       ((interp-R1 '()) e)])))

(define (run-R1 e)
  ((interp-R1 '()) e))

;; Test

(module+ test
  (check-eq? (run-R1 '(program (let ([x (+ 1 2)])
                                 (let ([y (+ 2 3)])
                                   (+ x y)))))
             8)
  )


;; uniquify makes all varaibles use different names.
;; R1 ==> R1
(define (uniquify alist)
  (λ (e)
    (match e
      [(? symbol?) (lookup e alist)]
      [(? integer?) e]
      ['(read) e]
      [`(let ([,x ,e]) ,body)
       (define new-x (gensym x))
       (define new-alist (cons (cons x new-x) alist))
       `(let ([,new-x ,((uniquify new-alist) e)])
          ,((uniquify new-alist) body))]
      [`(program ,e)
       `(program ,((uniquify alist) e))]
      [`(,op ,es ...)
       `(,op ,@(map (uniquify alist) es))])))

(module+ test
  ((uniquify '()) '(program (let ([x 32])
                              (+ (let ([x 10]) x) x))))
  ((uniquify '()) '(program (let ([x (let ([x 4])
                                       (+ x 1))])
                              (+ x 2))))
  )

(define (map3 f lst)
  (cond [(empty? lst)
         (values '() '() '())]
        [else
         (define-values (x y z) (f (first lst)))
         (define-values (xs ys zs) (map3 f (rest lst)))
         (values (cons x xs) (cons y ys) (cons z zs))]))

#| The C0 intermediate language
arg  ::= int | var
exp  ::= arg | (read) | (- arg) | (+ arg arg)
stmt ::= (assign var exp) | (return arg)
C0   ::= (program (var*) stmt+)
|#

;; flatten transforms nested expressions to flat expressions,
;; it returns a tuple, 1) the newly flattened expression, 2)
;; a list of assignment statements, 3) a list of variables
;; R1 ==> C0
(define (flatten e)
  (match e
    [(? number?) (values e '() '())]
    [(? symbol?) (values e '() '())]
    ['(read) (values e '() '())]
    [`(let ([,x ,e]) ,body)
     (define-values (e-flat e-asgn e-vars) (flatten e))
     (define new-asgn (append e-asgn `((assign ,x ,e-flat))))
     (define-values (body-flat body-asgn body-vars) (flatten body))
     (values body-flat (append new-asgn body-asgn) (append e-vars (cons x body-vars)))]
    [`(program ,e)
     (define-values (e-flat e-asgn e-vars) (flatten e))
     `(program ,e-vars
               ,@(append e-asgn `((return ,e-flat))))]
    [`(,op ,es ...)
     (define-values (es-flat es-asgn es-vars) (map3 flatten es))
     (define es-asgn* (apply append es-asgn))
     (define es-vars* (apply append es-vars))
     (define new-var (gensym 'tmp))
     (define asgn-stmt `(assign ,new-var ,(cons op es-flat)))
     (values new-var
             (append es-asgn* (list asgn-stmt))
             (cons new-var es-vars*))]))

(module+ test
  (flatten '(program (+ 52 (- 10))))
  (flatten '(program (let ([x (+ (- 10) 11)]) (+ x 41))))
  (flatten '(program (let ([a 42]) (let ([b a]) b))))
  (flatten '(program (+ (+ (+ 5 3) 2) (+ 3 (+ 7 8)))))
  )

#| A subset of X86 instructions (AT&T Syntax)
reg   ::= rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi
        | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
arg   ::= $int | %reg | int(%reg)
instr ::= addq arg,arg | subq arg,arg | negq arg | movq arg,arg
        | callq label | pushq arg | popq arg | retq
prog  ::= .global main
        | main: instr+
|#

#| Abstract syntax for x86 assembly
register ::= rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi
           | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15
arg      ::= (int n) | (reg register) | (deref register n)
instr    ::= (addq arg arg) | (subq arg arg) | (movq arg arg)
           | (retq) | (negq arg) | (callq label) | (pushq arg)
           | (popq arg)
x86_0    ::= (program n instr+)
|#

;; select-instr
;; C0 ==> X86*
(define (select-instr e)
  (match e
    [(? number?) `(int ,e)]
    [(? symbol?) `(var ,e)]
    [`(assign ,x (read))
     `((callq read_int)
       (movq (reg rax) (var ,x)))]
    [`(assign ,x ,(? number? n))
     `((movq (int ,n) (var ,x)))]
    [`(assign ,x (- ,arg))
     `((movq ,(select-instr arg) (var ,x))
       (negq (var ,x)))]
    [`(assign ,x (+ ,arg1 ,arg2))
     `((movq ,(select-instr arg1) (var ,x))
       (addq ,(select-instr arg2) (var ,x)))]
    [`(assign ,x ,y)
     `((movq (var ,y) (var ,x)))]
    [`(return ,arg)
     `((movq ,(select-instr arg) (reg rax)))]
    [`(program ,vars ,stmts ...)
     `(program ,vars ,@(apply append (map select-instr stmts)))]))

(module+ test
  (select-instr (flatten '(program (+ 52 (- 10))))))

;; assign-homes
;; X86* ==> X86
(define (assign-homes e)
  (define (offset vars x) (* -8 (+ 1 (index-of vars x))))
  (define (assign vars v)
    (match v
      [`(var ,x) `(deref rbp ,(offset vars x))]
      [`(addq ,e1 ,e2) `(addq ,(assign vars e1) ,(assign vars e2))]
      [`(subq ,e1 ,e2) `(subq ,(assign vars e1) ,(assign vars e2))]
      [`(movq ,e1 ,e2) `(movq ,(assign vars e1) ,(assign vars e2))]
      [`(negq ,e) `(negq ,(assign vars e))]
      [`(pushq ,e) `(pushq ,(assign vars e))]
      [`(popq ,e) `(popq ,(assign vars e))]
      [v v]))
  (match e
    [`(program ,vars ,stmts ...)
     `(program ,(length vars) ,@(map (λ (s) (assign vars s)) stmts))]))

(module+ test
  (assign-homes (select-instr (flatten '(program (+ 52 (- 10)))))))

;; patch-instr
;; X86 ==> X86
(define (patch-instr e)
  (define (patch inst)
    (match inst
      [`(,inst (deref rbp ,offset1) (deref rbp ,offset2))
       `((movq (deref rbp ,offset1) (reg rax))
         (,inst (reg rax) (deref rbp ,offset2)))]
      [inst (list inst)]))
  (match e
    [`(program ,vars ,stmts ...)
     `(program ,vars ,@(apply append (map patch stmts)))]))

(module+ test
  (patch-instr (assign-homes (select-instr (flatten '(program (+ 52 (- 10))))))))

;; print-X86
(define (print-x86 e)
  (define (arg->string arg)
    (match arg
      [(? symbol?) (symbol->string arg)]
      [`(int ,n) (string-append "$" (number->string n))]
      [`(reg ,r) (string-append "%" (symbol->string r))]
      [`(deref ,r ,offset)
       (string-append (number->string offset) "(%" (symbol->string r) ")")]))
  (define (inst->string inst)
    (match inst
      [`(,instr ,arg1 ,arg2)
       (string-append (symbol->string instr) " "
                      (arg->string arg1) ", "
                      (arg->string arg2) " ")]
      [`(,instr ,arg) (string-append (symbol->string instr) " " (arg->string arg))]
      [`(,instr) (symbol->string instr)]))
  (match e
    [`(program ,vars ,stmts ...)
     (define nstack (* vars 8))
     (define template
       ".global main
main:
  pushq %rbp
  movq %rsp, %rbp
  subq $~a, %rsp
  ~a
  movq %rax, %rdi
  callq print_int
  addq $~a, %rsp
  popq %rbp
  retq")
     (format template nstack (string-join (map inst->string stmts) "\n  ") nstack)]))

(define (compile-no-reg e)
  (print-x86 (patch-instr (assign-homes (select-instr (flatten ((uniquify '()) e)))))))

(display
 (compile-no-reg '(program (let ([v 1])
                      (let ([w 46])
                        (let ([x (+ v 7)])
                          (let ([y (+ 4 x)])
                            (let ([z (+ x w)])
                              (+ z (- y))))))))))

;; TODO: fix let which is generating redundant movq
(select-instr (flatten ((uniquify '()) '(program (let ([v 1])
                      (let ([w 46])
                        (let ([x (+ v 7)])
                          (let ([y (+ 4 x)])
                            (let ([z (+ x w)])
                              (+ z (- y)))))))))))
