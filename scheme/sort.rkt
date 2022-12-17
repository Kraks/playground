#lang racket

;; Merge sort algorithm in Racket

(define merge
  (lambda (xs ys)
    (cond [(null? xs) ys]
          [(null? ys) xs]
          [(< (car xs) (car ys))
           (cons (car xs) (merge (cdr xs) ys))]
          [else (cons (car ys) (merge xs (cdr ys)))])))

(define merge-sort
  (lambda (xs)
    (let ([m (quotient (length xs) 2)])
      (cond [(eq? (length xs) 1) xs]
            [else (merge (merge-sort (take xs m))
                         (merge-sort (drop xs m)))]))))

; test merge
(merge '(4 6 8) '(3 5 7))
; test merge-sort
(merge-sort '(9 7 5 3 1 10 9 8 12))

;; Quick sort algorithm in Racket
(define qsort
  (lambda (lst)
    (if (null? lst) '()
        (let ([lt (filter (lambda (y) (< y (car lst))) (cdr lst))]
              [gt (filter (lambda (y) (>= y (car lst))) (cdr lst))])
          (append (qsort lt) (list (car lst)) (qsort gt))))))

(define (qsort2 lst)
  (if (null? lst) '()
      `(,@(qsort (filter (curry >= (car lst)) (cdr lst)))
        ,(car lst)
        ,@(qsort (filter (curry < (car lst)) (cdr lst))))))

(qsort '(5 1 10 11 2))

;; Insertion sort algorithm in Racket
(define insert
  (lambda (ele xs)
    (if (null? xs) (list ele)
        (if (<= ele (car xs))
            (cons ele xs)
            (cons (car xs) (insert ele (cdr xs)))))))

(define insertion-sort
  (lambda (xs)
    (if (null? xs) '()
        (insert (car xs) (insertion-sort (cdr xs))))))

; test insert
(insert 5 '( 1 2 3 7))
; test insertion sort
(insertion-sort '(10 5 9 6 4 7 3 8 2 1))
