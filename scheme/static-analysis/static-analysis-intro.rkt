#lang racket

;; From Matt Might's blog post: What is static analysis?
;
; <prog> ::= <stmt> ...
; <stmt> ::= (label <label>)
;         |  (goto <label>)
;         |  (:= <var> <exp>)
;         |  (if <exp> goto <label>)

; <exp> ::= (+ <exp> <exp>)
;         | (* <exp> <exp>)
;         | (= <exp> <exp>)
;         | <int> | <var>

; add a while consturct to Racket
(define-syntax while
  (syntax-rules ()
    [(_ cond body ...)
     (letrec [(loop (lambda ()
                      (when cond
                        body ...
                        (loop))))]
       (loop))]))

; stmt-map : label => stmt*
(define stmt-map (make-hasheq))

; constructs the label-to-statments map
(define (preprocess stmts)
  (match stmts
    [(cons `(label ,label) rest)
     (hash-set! stmt-map label stmts)
     (preprocess rest)]
    [(cons _ rest)
     (preprocess rest)]
    ['() (void)]))

; states pair statements with environments
(struct state { stmts env })

; an environment maps variables to integers
(define env0 (make-immutable-hasheq))

; inject creates an inital state for program
(define (inject prog)
  (state prog env0))

;;;; Abstract

; states pair statements with environments
(struct astate { stmts aenv } #:transparent)

; an enviroment maps varibales to integers
(define aenv0 (make-immutable-hasheq))

; inject creates an initial state for a program
(define (ainject prog)
  (astate prog aenv0))

; α : integer -> abstract-integer
(define (a n)
  (cond 
    [(< n 0) {set '-}]
    [(= n 0) {set 0}]
    [(> n 0) {set '+}]))

; +/abstract : abstract-integer abstract-integer -> abstract-integer
(define (+/abstract an1 an2)
  (apply set-union
         (for*/list ([s1 an1]
                     [s2 an2])
           (+/a s1 s2))))

; +/a : sign sign -> abstract-integer
(define (+/a s1 s2)
  (match* (s1 s2)
    [('- '-) {set '-}]
    [('- 0)  {set '-}]
    [('- '+) {set '- 0 '+}]
    [('0 x)  {set x}]
    [('+ '-) {set '- 0 '+}]
    [('+ 0)  {set '+}]
    [('+ '+) {set '+}]))

; */abstract : abstract-integer abstract-integer -> abstract-integer
(define (*/abstract an1 an2)
  (apply set-union
         (for*/list ([s1 an1]
                     [s2 an2])
           (*/a s1 s2))))

; */a : sign sign -> abstract-integer
(define (*/a s1 s2)
  (match* (s1 s2)
    [('- '-) {set '+}]
    [('-  0) {set  0}]
    [('- '+) {set '-}]
    [('0  x) {set  0}]
    [('+ '-) {set '-}]
    [('+  0) {set  0}]
    [('+ '+) {set '+}]))

; exp-aeval : exp aenv -> abstract-integer
(define (exp-aeval exp aenv)
  (match exp
    [(? symbol?) (hash-ref aenv exp)]
    [(? integer?) (a exp)]
    [`(+ ,exp1 ,exp2)
     (+/abstract (exp-aeval exp1 aenv)
                 (exp-aeval exp2 aenv))]
    [`(* ,exp1 ,exp2)
     (*/abstract (exp-aeval exp1 aenv)
                 (exp-aeval exp2 aenv))]
    [`(= ,exp1 ,exp2)
     {set 0 '+}]))

(define (astate->string astate)
  (if (pair? (astate-stmts astate))
      (format "stmt: ~a~nenv: ~a~n"
              (car (astate-stmts astate))
              (astate-aenv astate))
      "end~n"))

; astep : astate -> astate*
(define (astep astate0)
  (define stmts (astate-stmts astate0))
  (define aenv (astate-aenv astate0))
  (match stmts
    ['() aenv]
    [(cons `(label ,l) rest)
     (list (astate rest aenv))]
    [(cons `(:= ,var ,exp) rest)
     (define aenv* (hash-set aenv var (exp-aeval exp aenv)))
     (list (astate rest aenv*))]
    [(cons `(if ,exp goto ,label) rest)
     (define condition (exp-aeval exp aenv))
     (list
      (astate (hash-ref stmt-map label) aenv)
      (astate rest aenv))]
    [(cons `(goto ,label) rest)
     (list (astate (hash-ref stmt-map label) aenv))]
    [else
     (error (format "unknown instruction: ~a!" (car stmts)))]))

(define (analyze prog)
  (preprocess prog)
  ; the initial abstract state
  (define astate0 (ainject prog))
  ; the set of all states ever seen
  (define visited (set))
  ; the neighbor maps
  (define neighbors (make-hasheq))
  ; mark the neighbors of a state
  (define (mark-neighbors! astate succs)
    (hash-set! neighbors astate succs))
  ; makr a state as seen
  (define (mark-seen! astate)
    (set! visited (set-add visited astate)))
  ; check if a state is seen
  (define (seen? astate)
    (set-member? visited astate))
  ; states to explore next
  (define todo (list astate0))
  ; adds states to be explored
  (define (push-todos astates)
    (set! todo (append astates todo)))
  ; grabs the next state to be explored
  (define (pop-todo)
    (define next (car todo))
    (set! todo (cdr todo))
    next)
  
  (while (not (null? todo))
         (define curr (pop-todo))
         (when (not (seen? curr))
           (mark-seen! curr)
           (define succs (astep curr))
           (when (list? succs)
             (mark-neighbors! curr succs)
             (push-todos succs))))
  ; return all visited states
  neighbors)

; test
(define test-prog
  '(
    (:= n 5)
    (:= a 1)
    (label top)
    (if (= n 0) goto done)
    (:= a (* a n))
    (:= n (+ n -1))
    (goto top)
    (label done)))

(define test-prog1
  '((:= n 5)
    (label done)))

(analyze test-prog1)
