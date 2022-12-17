#lang racket

#|
在计算机语言中，把文本parse之后得到了AST，而语义可理解为是由Interpreter来定义的，
是interpretation的过程赋予了一段程序meaning。这个东西也叫做Definitional Interpreter。
但是解释一段计算机语言代码，生成的是Value。

这个过程可以对应到自然语言中，语言文本parse之后得到AMR的结构正好对应AST，
而对AMR进行解释的过程则是spelling生成出sentence的过程。

Natural Lang --parse--> AMR/CCG --interp--> sentence
Computer PL  --parse-->   AST   --interp--> value

这个过程可以很好地对应起来，甚至我感觉计算机语言的解释器结构（比如CEK Machine）
也可以在NPL中有一个对应。
|#

; 定义对应于AMR中的结构
(struct Want (arg0 arg1) #:transparent)
(struct Believe (arg0 arg1) #:transparent)
(struct Boy () #:transparent)
(struct Girl () #:transparent)

; a-sentence是一个句子的结构
(define a-boy (Boy))
(define a-sentence (Want a-boy (Believe (Girl) a-boy)))

; interp就是在把这个结构还原成句子文本
(define (interp s)
  (match s
    [(Want sb sth) (string-append (interp sb)
                                  " desires "
                                  (interp sth))]
    [(Believe sb sth) (string-append (interp sb)
                                     " believes "
                                     (interp sth))]
    [(Boy) "the boy"]
    [(Girl) "the girl"]))

; "the boy desires the girl believes the boy"
(interp a-sentence)