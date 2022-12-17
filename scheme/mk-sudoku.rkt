#lang racket

(require math/base)
(require minikanren)
(require minikanren/numbers)


(define mk-num->dec
  (letrec ((mk-num->dec*
            (lambda (ns idx acc)
              (cond [(null? ns) acc]
                    [else (mk-num->dec*
                           (cdr ns)
                           (+ 1 idx)
                           (+ acc (* (car ns) (expt 2 idx))))]))))
    (lambda (ns) (mk-num->dec* ns 0 0))))

(define mapo
  (lambda (fo xs ys)
    (conde
     [(== '() xs)
      (== '() ys)]
     [(fresh (x xs^ y ys^)
             (== `(,x . ,xs^) xs)
             (== `(,y . ,ys^) ys)
             (fo x y)
             (mapo fo xs^ ys^))])))

(define foldlo
  (lambda (fo acc xs res)
    (conde
     [(== '() xs)
      (== acc res)]
     [(fresh (x xs^ acc^)
             (== `(,x . ,xs^) xs)
             (fo x acc acc^)
             (foldlo fo acc^ xs^ res))])))

(define foldro
  (lambda (fo acc xs res)
    (conde
     [(== '() xs)
      (== acc res)]
     [(fresh (x xs^ acc^)
             (== `(,x . ,xs^) xs)
             (foldro fo acc xs^ acc^)
             (fo x acc^ res))])))

(define pluso*
  (lambda (xs sum) (foldlo pluso (build-num 0) xs sum)))

(define (transpose grid)
  (if (null? grid) '()
      (map (λ (i) (map (λ (line) (list-ref line i)) grid))
           (range (length (car grid))))))

(define get-col (λ (g i) (map (λ (line) (list-ref line i)) g)))

(define (get-block grid M N row col)
  (let ([row (add1 (floor (/ row N)))]
        [col (floor (/ col M))])
    (foldl append '() (for/list ([i (range (* (sub1 row) N) (* row N))])
                        (take (drop (list-ref grid i) (* col M)) M)))))

(define (each-block grid M N)
  (foldl append '()
         (for/list ([row (range 0 (* M N) N)])
           (for/list ([col (range 0 (* M N) M)])
             (get-block grid M N row col)))))

(define get-used-num (curry filter (λ (x) (not (eq? '_ x)))))

(define (grid-get grid row col) (list-ref (list-ref grid row) col))

(define (grid-set grid row col ele)
  (list-set grid row (list-set (list-ref grid row) col ele)))

(define (to-mk-num g)
  (map (lambda (line)
         (map (lambda (x) (if (number? x) `(build-num ,x) x))
              line))
       g))

(define (solve grid M N)
  (define side-length (* M N))
  (define total (sum (range 1 (add1 side-length))))
  (define (end? row col) (and (= side-length row) (= 0 col)))
  (define (next-row row col)
    (if (zero? (modulo (add1 col) side-length)) (add1 row) row))
  (define (next-col row col)
    (if (zero? (modulo (add1 col) side-length)) 0 (add1 col)))
  (define (gen-name row col)
    (string->symbol (string-append "m"
                                   (number->string row)
                                   (number->string col))))
  (define (gen-fresh-name-for-holes g row col)
    (cond [(end? row col) g]
          [(equal? '_ (grid-get g row col))
           (gen-fresh-name-for-holes
            (grid-set g row col (gen-name row col))
            (next-row row col) (next-col row col))]
          [else
           (gen-fresh-name-for-holes g (next-row row col) (next-col row col))]))
  (define (extract-holes g)
    (flatten (map (λ (lst) (filter (λ (l) (not (list? l))) lst)) g)))
  
  (define g* (gen-fresh-name-for-holes (to-mk-num grid) 0 0))
  (define holes (extract-holes g*))

  `(run 1 ,holes
        ,@(for/list ([line g*]) `(pluso* (list ,@line) (build-num ,total)))
        ,@(for/list ([line (transpose g*)]) `(pluso* (list ,@line) (build-num ,total)))
        ,@(for/list ([block (each-block g* M N)]) `(pluso* (list ,@block) (build-num ,total)))))

(define grid
  '([3 _ 6  5 _ 8  4 _ _]
    [5 2 _  _ _ _  _ _ _]
    [_ 8 7  _ _ _  _ 3 1]
    [_ _ 3  _ 1 _  _ 8 _]
    [9 _ _  8 6 3  _ _ 5]
    [_ 5 _  _ 9 _  6 _ _]
    [1 3 _  _ _ _  2 5 _]
    [_ _ _  _ _ _  _ 7 4]
    [_ _ 5  2 _ 6  3 _ _]))

(define easy-grid
  '((3 1 _  5 _ 8  4 9 2) ;6 7 2
    (5 2 9  1 3 4  7 6 8)
    (4 8 7  6 2 9  5 3 1)
    (2 6 3  4 1 5  9 8 7)
    (9 7 4  8 6 3  1 2 5)
    (8 5 1  7 9 2  6 4 3)
    (1 3 8  9 4 7  2 5 6)
    (6 9 2  3 _ 1  8 7 4) ;5
    (7 4 5  2 8 6  3 1 9)))

(define-namespace-anchor mk-sudoku)
;(solve grid 3 3)

(eval (solve easy-grid 3 3)
      (namespace-anchor->namespace mk-sudoku))