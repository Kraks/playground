#lang br/quicklang

(define (read-syntax path port)
  (define args (port->lines port))
  (define arg-datums (filter-not void? (format-datums '~a args)))
  (display arg-datums)
  (define module-datum `(module stacker-mod "funstacker.rkt"
                          (handle-args ,@arg-datums)))
  (datum->syntax #f module-datum))

(provide read-syntax)

(define-macro (funstacker-module-begin HANDLE-ARGS-EXPR)
   #'(#%module-begin
      (display (first HANDLE-ARGS-EXPR))))

(provide (rename-out [funstacker-module-begin #%module-begin]))

(define (handle-args . args)
  (for/fold ([stack-acc empty])
            ([arg args])
    (cond [(number? arg) (cons arg stack-acc)]
          [(or (equal? * arg) (equal? + arg))
           (define op-result
             (arg (first stack-acc) (second stack-acc)))
           (cons op-result (drop stack-acc 2))])))
(provide handle-args)
(provide + *)