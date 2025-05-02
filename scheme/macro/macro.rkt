#lang racket

(require (for-syntax racket/match))

; Chapter 3 Transform

; define a transformer binding
(define-syntax foo
  (lambda (stx) (syntax "I am foo")))

(define-syntax (also-foo stx)
  (syntax "I am also foo"))

; #' is the shorthand for `syntax`
(define-syntax (quoted-foo stx)
  #'"I am also foo, using #' instead of syntax")

(define-syntax (say-hi stx)
  #'(display "hi"))

(define-syntax (show-me stx)
  (print stx)
  #'(void))

(define stx #'(if x (list "true") #f))
(syntax-source stx)
(syntax-line stx)
(syntax-column stx)
(syntax->datum stx)
(syntax-e stx)
(syntax->list stx) ;same as syntax-e

(define-syntax (reverse-me stx)
  (datum->syntax stx (reverse (cdr (syntax->datum stx)))))

(reverse-me "backwards" "am" "i" values)

(define-syntax (our-if stx)
  (define xs (syntax->list stx))
  (datum->syntax stx `(cond [,(cadr xs) ,(caddr xs)]
                            [else ,(caddr xs)])))

(define-syntax (our-if-match stx)
  (match (syntax->list stx)
    [`(,name ,cnd ,thn ,els)
     (datum->syntax stx `(cond [,cnd ,thn]
                               [else ,els]))]))

(our-if-match #t "true" "false")

(begin-for-syntax
  ; some helper function that can be used during compile time
  )

; Chapter 4 Pattern matching
