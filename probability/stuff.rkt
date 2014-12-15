#lang racket/base

(provide (all-defined-out))

(require racket/list
         racket/set
         racket/contract/base
         )

(define (immhasheq/c kc vc)
  (and/c hash-eq? (hash/c kc vc #:immutable #t)))

(define (muthasheq/c kc vc)
  (and/c hash-eq? (hash/c kc vc #:immutable #f)))

(define (muthasheq . args)
  (hash-copy (apply hasheq args)))

(define (hash->immhasheq hsh)
  (make-immutable-hasheq (hash->list hsh)))

(define-syntax-rule
  (for/mhasheq (for-clause ...) body ...)
  (hash-copy (for/hasheq (for-clause ...) body ...)))

(define (set-add* s vs)
  (cond [(empty? vs) s]
        [else (set-add* (set-add s (first vs)) (rest vs))]))
