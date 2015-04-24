#lang racket

(require racket/match
         my-cond
         "../probability.rkt"
         "../match-hash-member.rkt"
         "../stuff.rkt"
         )
(module+ test
  (require rackunit))

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
(define-syntax given-has-brv? (make-rename-transformer #'hash-has-key?))
(define empty-given (given))

(define (get-p A gvn)
  (match A
    [(? probability? A) (->pn A)]
    [(match-hash-member gvn A v)
     (match (->pn v)
       [1 1]
       [0 0]
       [k (eprintf "get-p: I don't even know what the shape of a Given is supposed to be yet\n") k])]
    [(brv name deps proc)
     (my-cond
       [(set-empty? deps) (proc empty-given)]
       #:def (define gvn-dep-A
               (for/given ([(B B?) (in-given gvn)]
                           #:when (B . depends-on? . A))
                          (values B B?)))
       #:def (define other-gvn (hash-remove* gvn (hash-keys gvn-dep-A)))
       ;; P(A|B) = P(A and B) / P(B)
       ;; P(A|{B and C}) = P(A and B and C) / P(B and C)
       [(given-empty? gvn-dep-A)
        (define gvn-deps
          (for/given ([B (in-set deps)] ;#:when (B . depends-on? . gvn)
                      )
            (values B (get-p B gvn))))
        (proc gvn-deps)]
       [else
        (define B*C
          (apply brv-and
                 (for/list ([(B B?) (in-given gvn-dep-A)])
                   (match B?
                     [1 B]
                     [0 (brv-not B)]))))
        (define P-A*B*C
          (get-p (brv-and A B*C) other-gvn))
        (define P-B*C
          (get-p B*C other-gvn))
        (cond [(zero? P-B*C)
               (unless (zero? P-A*B*C) (error 'bad "very bad"))
               (eprintf "warning: get-p: cann't infer P, returning +nan.0\n")
               +nan.0]
              [else
               (/ P-A*B*C P-B*C)])]
       )]))

(define (B . depends-on? . A)
  (match B
    [(? probability? B) #f]
    [(brv name deps proc)
     (match A
       [(brv _ _ _)
        (for/or ([dep (in-set deps)])
          (or (eq? dep A)
              (dep . depends-on? . A)))]
       [(? hash? A)
        (for/or ([A (in-hash-keys A)])
          (B . depends-on? . A))])]))

(define brv-and
  (case-lambda
    [() true]
    [(A) A]
    [(A B)
     (cond [(A . depends-on? . B)
            (when (B . depends-on? . A) (error 'bad "very bad"))
            (brv-and B A)]
           [else
            (brv #f (list A B)
                 (lambda (gvn)
                   (define P-A (hash-ref gvn A))
                   (define P-B (get-p B (hash-remove (hash-set gvn A #t) B)))
                   (pand P-A P-B)))])]
    ))

(define (brv-not v)
  (error '....))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (test-case "thing"
    (define (new-brv p) (brv #f '() (λ (gvn) p)))
    (define A (brv 'A '() (λ (gvn) 1/2)))
    (define B (brv 'B (seteq A) (λ (gvn) (pif* (get-p A gvn) 2/3 1/3))))
    (check-equal? (get-p A empty-given) 1/2)
    (check-equal? (get-p B empty-given) 1/2)
    (check-equal? (get-p B (given A 1)) 2/3)
    (check-equal? (get-p B (given A 0)) 1/3)
    (check-equal? (get-p (brv-and A B) empty-given) 1/3) ; (and A (if A 2/3 1/3)) = 1/2 * 2/3
    (check-equal? (get-p (brv-and B A) empty-given) 1/3)
    )
  )
