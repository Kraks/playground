#lang racket

(require rackunit)

#|
pattern ::= ∅           ;; empty
          | ()           ;; empty string
          | <symbol>     ;; single symbol
          | (p1 ++ p2)   ;; concatenation
          | (p1 || p2)   ;; union
          | (p *)        ;; zero or more occurrences, i.e., Kleene star
          | (p +)        ;; one or more occurrences, i.e., Kleene plus
          | (p ?)        ;; zero or one occurrence
|#

(define (symbol-length s)
  (string-length (symbol->string s)))

(define (first-char-eq? sym str)
  (string=? (symbol->string sym)
            (substring str 0 1)))

(define (accept reg str k)
  (match reg
    ['∅ #f]
    ['() (k str)]
    [(? symbol?) #:when (eq? (symbol-length reg) 1)
     (if (zero? (string-length str)) #f
         (and (first-char-eq? reg str)
              (k (substring str 1))))]
    [`(,r1 ++ ,r2) (accept r1 str (λ (s*) (accept r2 s* k)))]
    [`(,r1 || ,r2) (or (accept r1 str k) (accept r2 str k))]
    [`(,r *) (accept-star r str k)]
    [`(,r +) (accept r str (λ (s*) (and (not (eq? str s*))(accept-star reg s* k))))]
    [`(,r ?) (or (accept r str k) (k str))]))

(define (accept-star reg str k)
  (or (k str)
      (accept reg str
              (λ (s*) (and (not (string=? str s*))
                           (accept-star reg s* k))))))

(define (regmatch? reg str)
  (accept reg str (λ (s*) (zero? (string-length s*)))))

(check-true (regmatch? '(a ++ (b ++ c)) "abc"))
(check-true (regmatch? '() ""))
(check-true (regmatch? '((a *) +) "aaa"))
(check-true (regmatch? '(a ?) "a"))
(check-true (regmatch? '(a ?) ""))
(check-true (regmatch? '((a ++ (b *)) ++ ((c ?) || (d +))) "abbddd"))
(check-true (regmatch? '(a ++ (b || c)) "ab"))
(check-true (regmatch? '((a +) +) "aaa"))
(check-true (regmatch? '((a +) +) "aaaaaaaaaaaaa"))
(check-true (regmatch? '((a *) *) "aaaaa"))

(check-false (regmatch? '∅ "abc"))
(check-false (regmatch? '() "a"))
(check-false (regmatch? '((a *) +) "aa!"))
(check-false (regmatch? '((a +) *) "aa!"))
(check-false (regmatch? '(a ++ (b || c)) "aab"))
(check-false (regmatch? '(a ++ (b || ((c *) ?))) "acccccd"))
(check-false (regmatch? '((a +) +) "aaaaaaaaaaaa!"))