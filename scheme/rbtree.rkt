#lang racket

;; http://kimball.germane.net/germane2014deletion.pdf
;; http://matt.might.net/articles/red-black-delete/

;; shape invariant

;; An empty red-black tree is always black.
;; 1) Every descent sequence within a tree contains exactly the same
;;    number of black subtrees.
;; 2) The number of red subtrees in a descent sequence is less or equal
;;    to the number of black ones.

;; A red-black tree can be colored red only if both its subtree are black.

; struct definition for sorted-map
(define-struct sorted-map (compare))

; Internal nodes
(define-struct (T sorted-map)
  (color left key value right))

; Leaf nodes
(define-struct (L sorted-map) ())

; Double-black leaf nodes
(define-struct (BBL sorted-map) ())

; Matches internal nodes
(define-match-expander T!
  (syntax-rules ()
    [(_)           (T _ _ _ _ _ _)]
    [(_ l r)       (T _ _ l _ _ r)]
    [(_ c l r)     (T _ c l _ _ r)]
    [(_ l k v r)   (T _ c l _ _ r)]
    [(_ c l k v r) (T _ c l k v r)]))

; Matches leaf nodes
(define-match-expander L!
  (syntax-rules ()
    [(_) (L _)]))

; Matches black nodes (leaf or internal)
(define-match-expander B
  (syntax-rules ()
    [(_)            (or (T _ 'B _ _ _ _)
                        (L _))]
    [(_ cmp)        (or (T cmp 'B _ _ _ _)
                        (L cmp))]
    [(_ l r)         (T _ 'B l _ _ r)]
    [(_ l k v r)     (T _ 'B l k v r)]
    [(_ cmp l k v r) (T cmp 'B l k v r)]))

; Matches red nodes:
(define-match-expander R
  (syntax-rules ()
    [(_)             (T _ 'R _ _ _ _)]
    [(_ cmp)         (T cmp 'R _ _ _ _)]
    [(_ l r)         (T _ 'R l _ _ r)]
    [(_ l k v r)     (T _ 'R l k v r)]
    [(_ cmp l k v r) (T cmp 'R l k v r)]))

; Matches negative black nodes:
(define-match-expander -B
  (syntax-rules ()
    [(_)             (T _ '-B _ _ _ _)]
    [(_ cmp)         (T cmp '-B _ _ _ _)]
    [(_ l k v r)     (T _ '-B l k v r)]
    [(_ cmp l k v r) (T cmp '-B l k v r)]))

; Matches double-black nodes (leaf or internal):
(define-match-expander BB
  (syntax-rules ()
    [(_)             (or (T _ 'BB _ _ _ _)
                         (BBL _))]
    [(_ cmp)         (or (T cmp 'BB _ _ _ _)
                         (BBL _))]
    [(_ l k v r)     (T _ 'BB l k v r)]
    [(_ cmp l k v r) (T cmp 'BB l k v r)]))