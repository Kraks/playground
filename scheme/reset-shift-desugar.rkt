#lang racket

(require racket/control)

(+ 1 (reset (+ 2 (shift k (k (k 2))))))

;; ==>

(+ 1 (reset ((lambda (k) (k (k 2)))
             (lambda (v) (reset (+ 2 v))))))

;; ==>

(+ 1 ((lambda (k) (k (k 2)))
      (lambda (v) (+ 2 v))))

;;;;;;;;;;;;;;;;

(reset (+ 1 (shift a (a 1)) (shift b (b (b 1)))))

;; ==>

(reset ((lambda (a) (a 1))
        (lambda (v) (reset (+ 1 v (shift b (b (b 1))))))))

;; ==>

(reset ((lambda (a) (a 1))
        (lambda (v1) (reset ((lambda (b) (b (b 1)))
                             (lambda (v2) (reset (+ 1 v1 v2))))))))

;; ==>

((lambda (a) (a 1))
 (lambda (v1) ((lambda (b) (b (b 1)))
               (lambda (v2) (+ 1 v1 v2)))))

;;;;;;;;;;;;;;;;;;;;;;;
