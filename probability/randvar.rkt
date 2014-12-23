#lang racket/base

(provide extend-given
         given/c
         )

(require racket/match
         racket/list
         racket/sequence
         racket/set
         racket/contract/base
         racket/contract/region
         unstable/hash
         (only-in plot/private/contracted/math ivl ivl? ivl-min ivl-max)
         sugar/debug
         "probability.rkt"
         "pevt.rkt"
         "stuff.rkt"
         (for-syntax racket/base
                     ))
(module+ test-stuff
  (require rackunit (submod "pevt.rkt" test-stuff))
  (provide (all-defined-out) (all-from-out rackunit (submod "pevt.rkt" test-stuff))))
(module+ test
  (require (submod ".." test-stuff)))

(define-syntax (line stx)
  #`#,(syntax-line stx))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; for all A :
(struct discrete-randvar (possible-values get-probability-distribution get-implies))
;; possible-values : (Sequenceof A)
;; get-probability-distribution : [Given -> (A -> Pevt)]
;; get-implies : [A -> Given]

(struct continuous-randvar (possible-values get-probability-distribution get-implies))
;; possible-values : (Sequenceof Ivl)
;; get-probability-distribution : [Given -> (Real -> Probability)]
;; get-implies : [Real -> Given]

(define (get-discrete-probability-distribution randvar given)
  (let ([given (extend-given given)] [nf (gensym 'not-found)])
    (define gv (hash-ref given randvar nf))
    (match-define (discrete-randvar possible-values get-probability-distribution get-implies) randvar)
    (cond [(eq? gv nf)
           (define randvar-distribution
             (get-probability-distribution given))
           (define (distribution value)
             (define (v? x) (eq? x value))
             (cond [(sequence-ormap v? possible-values)
                    (randvar-distribution value)]
                   [else 0]))
           distribution]
          [else
           (define (distribution value)
             (cond [(eq? value gv) 1]
                   [else 0]))
           distribution])))

(define (get-continuous-probability-distribution randvar given)
  ((continuous-randvar-get-probability-distribution randvar) given))

(define (discrete-randvar-has-value->probability randvar value given)
  (define (v? x) (eq? x value))
  (cond [(sequence-ormap v? (discrete-randvar-possible-values randvar))
         ((get-discrete-probability-distribution randvar given) value)]
        [else 0]))

(define (discrete-randvar-has-value->pevt randvar value)
  (match-define (discrete-randvar possible-values get-probability-distribution get-implies) randvar)
  (define (v? x) (eq? x value))
  (cond [(sequence-ormap v? possible-values)
         (pevt (lambda (given)
                 ((get-discrete-probability-distribution randvar given) value))
               (hash-copy (hash-set (get-implies value) randvar value))
               (muthasheq))]
        [else (->pevt 0)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (randvar? x)
  (or (discrete-randvar? x)
      (continuous-randvar? x)
      (pevt? x)))

(define (->discrete-randvar x)
  (cond [(discrete-randvar? x) x]
        [(continuous-randvar? x) (error)]
        [(pevt? x) (discrete-randvar '(#t #f)
                                     (lambda (given)
                                       (lambda (v)
                                         (match v
                                           [#t (get-p x given)]
                                           [#f (pnot (get-p x given))])))
                                     (lambda (v)
                                       (hasheq x v)))]
        [else (discrete-randvar (list x)
                                (lambda (given)
                                  (lambda (v)
                                    (if (eq? v x) 1 0)))
                                (lambda (v) (hasheq)))]))

(define (randvar-result-implies randvar result)
  (match randvar
    [(discrete-randvar _ _ get-implies)
     (get-implies result)]
    [(continuous-randvar _ _ get-implies)
     (get-implies result)]
    [(pevt _ true-implies false-implies)
     (match result
       [#t true-implies]
       [#f false-implies])]))

(define given/c
  (flat-named-contract
   'given/c
   (immhasheq/c randvar? any/c)))

(define/contract (extend-given given [already-seen (seteq)])
  [(or/c pevt? given/c) . -> . given/c]
  (cond
    [(pevt? given) (extend-given (hasheq given #t) already-seen)]
    [(hash? given)
     (define new-already-seen (set-add* already-seen (hash-keys given)))
     (define lst
       (for/list ([(e b) (in-hash given)] #:when (not (set-member? already-seen e)))
         (extend-given (hash->immhasheq (randvar-result-implies e b)) new-already-seen)))
     (apply hash-union given lst
            #:combine/key (lambda (k v1 v2)
                            (cond [(eq? v1 v2) v1]
                                  [else "!!!" v2])))]
    [else (error 'extend-given "expected (immhasheq/c randvar? any/c), given: ~v" given)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (discrete-randvar=* rv1 rv2)
  (let ([rv1 (->discrete-randvar rv1)] [rv2 (->discrete-randvar rv2)])
    (define rv1.vs (discrete-randvar-possible-values rv1))
    (define rv2.vs (discrete-randvar-possible-values rv2))
    (apply
     eor
     (for/list ([v (in-list (remove-duplicates (sequence->list (sequence-append rv1.vs rv2.vs))))])
       (eand (discrete-randvar-has-value->pevt rv1 v)
             (discrete-randvar-has-value->pevt rv2 v))))))

(define (make-choice-randvar vs)
  (define n (length vs))
  (define 1/n (/ n))
  (discrete-randvar vs
                    (λ (given) (λ (v) 1/n))
                    (λ (v) (hasheq))))
                        

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (test-case "simpler"
    (define rv1 (make-choice-randvar '(heads tails)))
    (check-e= (discrete-randvar=* rv1 'heads) 1/2)
    (check-e= (discrete-randvar=* rv1 'tails) 1/2)
    (check-e= (get-p (discrete-randvar=* rv1 'heads)
                     (hasheq rv1 'heads))
              1)
    (check-e= (get-p (discrete-randvar=* rv1 'heads) (hasheq rv1 'tails)) 0)
    (check-e= (eand (discrete-randvar-has-value->pevt rv1 'heads)
                    (discrete-randvar-has-value->pevt rv1 'tails))
              0)
    (check-e= (eand (discrete-randvar-has-value->pevt rv1 'heads)
                    (discrete-randvar-has-value->pevt rv1 'heads))
              1/2)
    (check-e= (eor (discrete-randvar-has-value->pevt rv1 'heads)
                   (discrete-randvar-has-value->pevt rv1 'tails))
              1)
    (check-e= (eor (discrete-randvar-has-value->pevt rv1 'heads)
                   (discrete-randvar-has-value->pevt rv1 'heads))
              1/2))
  (test-case "Monty Hall probability"
    (define pz (make-choice-randvar '(a b c)))
    (define c1 (make-choice-randvar '(a b c)))
    (define sh (discrete-randvar '(a b c)
                                 (lambda (given)
                                   (lambda (v)
                                     (pand (pnot (discrete-randvar-has-value->probability c1 v given))
                                           (pnot (discrete-randvar-has-value->probability pz v given))
                                           )))
                                 (λ (v) (hasheq))))
    (define stick/switch (make-choice-randvar '(stick switch)))
    (define c2 (discrete-randvar '(a b c)
                                 (λ (given)
                                   (λ (v)
                                     (pif* (discrete-randvar-has-value->probability stick/switch 'stick given)
                                           (discrete-randvar-has-value->probability c1 v given)
                                           (pand (pnot (discrete-randvar-has-value->probability c1 v given))
                                                 (pnot (discrete-randvar-has-value->probability sh v given))))))
                                 (λ (v) (hasheq))))
    (define c2=pz
      (discrete-randvar=* pz c2))
    (check-equal? (get-p c2=pz (hasheq stick/switch 'stick)) 1/3)
    (check-equal? (get-p c2=pz (hasheq stick/switch 'switch)) 2/3)
    )
  )
