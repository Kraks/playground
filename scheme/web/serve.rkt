#lang racket

(require xml net/url)
(require racket/control)

(define (go)
  'yep-it-works)

(define (serve port-no)
  (define main-cust (make-custodian))
  (parameterize ([current-custodian main-cust])
    (define listener (tcp-listen port-no 5 #t))
    (define (loop)
      (accept-and-handle listener)
      (loop))
    (thread loop))
  (λ () (custodian-shutdown-all main-cust)))

(define (accept-and-handle listener)
  (define cust (make-custodian))
  ; 50MB
  (custodian-limit-memory cust (* 50 1024 1024))
  (parameterize ([current-custodian cust])
    (define-values (in out) (tcp-accept listener))
    (thread
     (λ ()
       (handle in out)
       (close-input-port in)
       (close-output-port out))))
  (thread (λ ()
            (sleep 10)
            (custodian-shutdown-all cust))))

(define (handle in out)
  ; match the first line to extract the request
  (define req
    (regexp-match #rx"^GET (.+) HTTP/[0-9]+\\.[0-9]+"
                  (read-line in)))
  (when req
    ; discard the rest of the header
    (regexp-match #rx"(\r\n|^)\r\n" in)
    ; dispatch
    (displayln req)
    (let ([xexpr (prompt (dispatch (list-ref req 1)))])
      ; send reply
      (display "HTTP/1.0 200 Okay\r\n" out)
      (display "Server: racket\r\nContent-Type: text/html\r\n\r\n" out)
      (display (xexpr->string xexpr) out))))

(define (dispatch str-path)
  ; parse the request as a URL
  (define url (string->url str-path))
  ; extract the path part
  (define path (map path/param-path (url-path url)))
  ; find a handler based on the path's first element
  (define h (hash-ref dispatch-table (car path) #f))
  (if h
      ; call a handler
      (h (url-query url))
      ; No handler found:
      `(html (head (title "Error"))
            (body
             (font ((color "red"))
                   "Unknown page: "
                   ,str-path)))))

(define dispatch-table (make-hash))

(hash-set! dispatch-table "hello"
           (lambda (query)
             `(html (body "Hello, World!"))))

(define (build-request-page label next-url hidden)
  `(html
    (head (title "Enter a Number to Add"))
    (body ([bgcolor "white"])
          (form ([action ,next-url] [method "get"])
                ,label
                (input ([type "text"] [name "number"]
                                      [value ""]))
                (input ([type "hidden"] [name "hidden"]
                                        [value ,hidden]))
                (input ([type "submit"] [name "enter"]
                                        [value "Enter"]))))))

(define (many query)
  (build-request-page "Number of greetings:" "/reply" ""))

(define (reply query)
  (define n (string->number (cdr (assq 'number query))))
  `(html (body ,@(for/list ([i (in-range n)])
                   " hello"))))

(hash-set! dispatch-table "many" many)
(hash-set! dispatch-table "reply" reply)

(define (send/suspend mk-page)
  (let/cc k
    (define tag (format "k~a" (current-inexact-milliseconds)))
    (hash-set! dispatch-table tag k)
    (abort (mk-page (string-append "/" tag)))))

(define (get-number label)
  (define query
    ; generate a url for the current compuation
    (send/suspend
     ; receive the computatin-as-url
     (λ (k-url)
       (build-request-page label k-url ""))))
  (string->number (cdr (assq 'number query))))

(define (sum2 query)
  (define m (get-number "First number:"))
  (define n (get-number "Second number:"))
  `(html (body "The sum is " ,(number->string (+ m n)))))
 
(hash-set! dispatch-table "sum2" sum2)