#lang br/quicklang

(define stack empty)

(define (pop-stack!)
  (define item (first stack))
  (set! stack (rest stack))
  item)

(define (push-stack! item)
  (set! stack (cons item stack)))

(define (handle [arg #f])
  (cond [(number? arg) (push-stack! arg)]
        [(or (equal? + arg) (equal? * arg))
         (define op-result (arg (pop-stack!) (pop-stack!)))
         (push-stack! op-result)]))

(define (read-syntax path port)
  (define src-lines (port->lines port))
  (define src-datums (format-datums '(handle ~a) src-lines))
  (define module-datum `(module stacker-mod "stacker.rkt"
                       ,@src-datums))
  (datum->syntax #f module-datum))

(define-macro (stacker-module-begin HANDLE-EXPR ...)
  #'(#%module-begin
     HANDLE-EXPR ...
     (display (first stack))))

(provide (rename-out [stacker-module-begin #%module-begin]))
(provide read-syntax)
(provide handle)
(provide * +)
