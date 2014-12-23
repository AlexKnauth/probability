#lang racket/base

(require racket/generic
         racket/splicing
         "probability.rkt"
         )

(define-generics random-variable
  [get-possible-values discrete-random-variable]
  [get-probability-distribution discrete-random-variable given]
  )

(define-generics continuous-random-variable
  [get-possible-values discrete-random-variable]
  [get-probability-distribution discrete-random-variable given]
  )
