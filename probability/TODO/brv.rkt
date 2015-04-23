#lang racket

(require racket/match
         my-cond
         "../probability.rkt"
         )

;; (and A B) = (and B A)
;; if B depends on A:
;; P(A) = (get-p A empty-given)
;; P(B|A) = (get-p B (given A #t))
;; P(A and B) = P(A)*P(B|A)
;; P(B and A) = P(B)*P(A|B) = P(A)*P(B|A)
;; P(A|B) = P(A and B) / P(B)

;; BRV stands for Boolean Random Variable
(struct brv (name deps proc) #:transparent)
;;   name : Symbol
;;   deps : (Setof BRV)
;;   proc : [Given -> Probability-Number]
;; If B depends on A, then A will be in the deps of B
;; But, while also A depends on B through [P(A|B) = P(A and B) / P(B)],
;; B will not be in the deps of A.

(define true  (brv 'true  '() (λ (_) 1)))
(define false (brv 'false '() (λ (_) 0)))

(define-syntax for/given (make-rename-transformer #'for/hasheq))
(define-syntax given (make-rename-transformer #'hasheq))
(define-syntax in-given (make-rename-transformer #'in-hash))
(define-syntax given-empty? (make-rename-transformer #'hash-empty?))
(define empty-given (given))

(define (get-p A gvn)
  (match A
    [(? probability? A) (->pn A)]
    [(brv name deps proc)
     (my-cond
       [(set-empty? deps) (proc empty-given)]
       #:def (define gvn-dep-A
               (for/given ([(B B?) (in-given gvn)]
                           #:when (B . depends-on? . A))
                          (values B B?)))
       ;; P(A|B) = P(A and B) / P(B)
       [(given-empty? gvn-dep-A)
        (error 'get-p "....")
        ]
       [else
        (error 'get-p "....")
        ]
       )]))

(define (B . depends-on? . A)
  (match B
    [(? probability? B) #f]
    [(brv name deps proc)
     (for/or ([dep (in-set deps)])
       (or (eq? dep A)
           (dep . depends-on? . A)))]))


