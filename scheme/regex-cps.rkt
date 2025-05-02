#lang racket

; <pat> ::= <string>
;         | (<pat> *)
;         | (<pat> +)
;         | (<pat> ?)
;         | (<pat> or <pat>)
;
; auxiliary function
(define (substring=? pat str start end)
  (for/and ([i (in-range start end)]
            [j (in-naturals)])
    (char=? (string-ref pat j) (string-ref str i))))

(define (aux pats k)
  (if (null? pats)
    (or k (λ (str pos) (= pos (string-length str))))
    (match (car pats)
      [(? string?)
       (let ([len (string-length (car pats))])
         (λ (str pos)
            (and (>= (string-length str) (+ pos len))
                 (substring=? (car pats) str pos (+ pos len))
                 ((aux (cdr pats) k) str (+ pos len)))))]
      [`(,p1 or ,p2) (λ (str pos)
                        (or ((aux `(,p1 ,@(cdr pats)) k) str pos)
                            ((aux `(,p2 ,@(cdr pats)) k) str pos)))]
      [`(,p *)
        (letrec ([m (λ (str pos)
                       (or ((aux `(,p) (λ (str pos) (m str pos))) str pos)
                           ((aux (cdr pats) k) str pos)))])
          m)]
      [`(,p +) (aux `(,p (,p *) ,@(cdr pats)) k)]
      [`(,p ?) (aux `((,p or "") ,@(cdr pats)) k)]
      [else (error "bad pattern")])))

; reg-match-cps : (listof pat) string -> boolean
(define (reg-match-cps pats str) ((aux pats #f) str 0))

(reg-match-cps '("a" ("b"*) (("c"?) or ("d"+))) "abbc")  ;#t
(reg-match-cps '("a" ("b" or "c")) "ab")                 ;#t
(reg-match-cps '("a" ("b" or (("c"*)?))) "accccc")       ;#t
(reg-match-cps '("a" ("b" or (("c"*)?))) "acccccd")      ;#f
(let ([in (string-append "abb" (make-string 1000000 #\d))])
  (time (reg-match-cps '("a" ("b"*) (("c"?) or ("d"+))) in)))

(reg-match-cps '((("a" *) *)) "aaaa!")
