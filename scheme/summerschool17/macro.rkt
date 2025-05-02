#lang racket

(require (for-syntax syntax/parse)
         (for-syntax racket/list))

(define-syntax (f stx) (syntax 5))

;(f 42)

(define-syntax (identity stx)
  (displayln '(hello world))
  stx)
;(identity 0)


(define-syntax (how-long-is stx)
  (define ls (syntax->list stx))
  (define len (length ls))
  (define line (syntax-line stx))
  (displayln line)
  (displayln (cdr ls))
  ;#`#,len)
  (quasisyntax (unsyntax len)))

;(how-long-is 1 2 3)

(define-syntax (hello stx)
  (define the-id (second (syntax->list stx)))
  (define def-tree (list 'define the-id ''world))
  (datum->syntax stx def-tree))

;(hello x)

(define-syntax (hello2 stx)
  (syntax-parse stx
    [(hello id:id) #'(define id 'world)]))

;(hello2 y)

(define-syntax (conj stx)
  (syntax-parse stx
    [(and lhs:expr rhs:expr)
     #'(if lhs rhs #false)]
    [(and lhs:expr mhs:expr rhs:expr ...)
     #'(if lhs (conj mhs rhs ...) #false)]))

;(conj 1 2 3 4)
;(conj #t #f)

(define-syntax (disj2 stx)
  (syntax-parse stx
    [(_ lhs:expr rhs:expr)
     #'(let ([lhsv lhs]) (if lhsv lhsv rhs))]))

(define-syntax (disj stx)
  (syntax-parse stx
    [(_ lhs:expr rhs:expr)
     #'(let ([lhsv lhs]) (if lhsv lhsv rhs))]
    [(_ lhs:expr rhs:expr rest:expr ...)
     #'(let ([lhsv lhs])
         (if lhsv lhsv (disj rhs rest ...)))]))

(define-syntax (block stx)
  (syntax-parse stx
    [(_ ((lhs:id rhs:expr)) body)
     #'((λ (lhs) body) rhs)]
    [(_ ((lhs1:id rhs1:expr) (lhs2:id rhs2:expr) ...) body)
     #'((λ (lhs1) (block ((lhs2 rhs2) ...) body)) rhs1)]))

(define helper
  (λ (i limit stride thunk)
    (when (< i limit)
      (begin (thunk i)
             (helper (+ i stride) limit stride thunk)))))

(define-syntax (for-loop stx)
  (syntax-parse stx
    [(_ ([i:id e0:expr limit:expr stride:expr]) body)
     #'(helper e0 limit stride (λ (i) body))]
    [(_ ([i:id e0:expr limit:expr]) body)
     #'(for-loop ([i e0 limit 1]) body)]))

;(for-loop ([x 0 5]) (displayln x))
;(for-loop ([x 0 5 2]) (displayln x))

;;==========================

#|
(define-syntax (lambda stx)
  (syntax-parse stx
    [(_ (x:id) e:expr)
     #'(cons 'x e)]))
|#

(define (f x) 1)

(define-syntax (orig-lambda stx)
  (syntax-parse stx
    [(_ (x:id) e:expr)
     #'(local [(define (new-f x) e)]
         new-f)]))

(define-syntax (new-lambda stx)
  (syntax-parse stx
    [(_ (x:id) e:expr)
     #'(lambda (x) (printf "arg: ~s\n" x) e)]))

(define-syntax (new-define stx)
  (syntax-parse stx
    [(_ (f:id arg:id) body)
     #'(define f (new-lambda (arg) body))]))

(new-define (g x) (+ x 1))

(define-syntax (new-#%app stx)
  (syntax-parse stx
    [(_ fun args ...)
     (define argslist (cdr (cdr (syntax->list stx))))
     (define rev-argslist (reverse argslist))
     #`(#%app fun #,@rev-argslist)]))