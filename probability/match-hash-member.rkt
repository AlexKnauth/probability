#lang racket/base

(provide match-hash-member)

(require racket/match
         (for-syntax racket/base
                     syntax/parse
                     ))
(module+ test
  (require rackunit))

(define-match-expander match-hash-member
  (syntax-parser
    [(match-hash-member hsh-expr:expr key-pat:expr val-pat:expr)
     #'(app (let ([hsh hsh-expr])
              (λ (k)
                (let/ec fail
                  (list k (hash-ref hsh k (λ () (fail #f)))))))
            (list key-pat val-pat))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (check-equal? (match 'k
                  [(match-hash-member (hash 'k 'v) k v)
                   (list k v)])
                '(k v))
  )
