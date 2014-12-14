#lang racket/base

(provide (struct-out pevt)
         pevtish?
         ->pevt
         get-p
         enot
         eand
         eor
         eif*
         )

(require racket/set
         racket/list
         racket/match
         racket/contract/base
         racket/contract/region
         syntax/parse/define
         unstable/hash
         my-cond
         "probability.rkt"
         (for-syntax racket/base
                     syntax/parse
                     ))
(module+ test
  (require rackunit))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (immhasheq/c kc vc)
  (and/c hash-eq? (hash/c kc vc #:immutable #t)))

(define (muthasheq/c kc vc)
  (and/c hash-eq? (hash/c kc vc #:immutable #f)))

(define (muthasheq . args)
  (hash-copy (apply hasheq args)))

(define (hash->immhasheq hsh)
  (make-immutable-hasheq (hash->list hsh)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (struct pevt (get-p true-implies false-implies) ....)

;; get-p : [(HashEqof Pevt Bool) -> Probability]
;; true-implies : (MutHashEqof Pevt Boolean)
;; false-implies : (MutHashEqof Pevt Boolean)
(struct pevt (get-p true-implies false-implies)) ; opaque

(define (pevtish? x)
  (or (pevt? x)
      (probability? x)))

;; ->pevt : Pevtish -> Pevt
(define/contract (->pevt x)
  [pevtish? . -> . pevt?]
  (cond [(pevt? x) x]
        [(probability? x)
         (define n (->pn x))
         (define (get-p _) n)
         (pevt get-p (muthasheq) (muthasheq))]
        [else (error '->pevt "expected pevtish?, given ~v" x)]))

(define/contract (extend-hsh hsh)
  [(immhasheq/c pevt? boolean?) . -> . (immhasheq/c pevt? boolean?)]
  (define lst
    (for/list ([(e b) (in-hash hsh)])
      (match b
        [#t (extend-hsh (hash->immhasheq (pevt-true-implies e)))]
        [#f (extend-hsh (hash->immhasheq (pevt-false-implies e)))])))
  (apply hash-union hsh lst
         #:combine/key (lambda (k v1 v2)
                         (cond [(eq? v1 v2) v1]
                               [else #;(printf "extend-hsh: !!! k: ~v, v1: ~v, v2: ~v\n" k v1 v2) v2]
                               ))))

;; get-p : Pevtish (HashEqof Pevt Boolean) -> Probability
(define/contract (get-p e hsh)
  [pevtish? (immhasheq/c pevt? boolean?) . -> . probability?]
  (let ([e (->pevt e)] [hsh (extend-hsh hsh)])
    (->pn
     (hash-ref hsh e
       (lambda ()
         (match-define (pevt get-p true-implies false-implies) e)
         (get-p hsh))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (enot e)
  (let ([e (->pevt e)])
    (pevt (lambda (hsh)
            (pnot (get-p e hsh)))
          (muthasheq e #f)
          (muthasheq e #t))))

(define eand-proc
  (case-lambda
    [() (->pevt 1)]
    [(e) (->pevt e)]
    [es (let ([es (map ->pevt es)])
          (pevt (lambda (hsh)
                  (let loop ([ps '()] [hsh hsh] [es es])
                    (cond [(empty? es) (apply pand (reverse ps))]
                          [else (let ([e (first es)])
                                  (loop (cons (get-p e hsh) ps)
                                        (hash-set hsh e #t)
                                        (rest es)))])))
                (hash-copy (for/hasheq ([e (in-list es)])
                             (values e #t)))
                (muthasheq)))]))

(define eor-proc
  (case-lambda
    [() (->pevt 0)]
    [(e) (->pevt e)]
    [(e1 e2) (let ([e1 (->pevt e1)] [e2 (->pevt e2)])
               (pevt (lambda (hsh)
                       (+ (get-p e1 hsh)
                          (get-p e2 hsh)
                          (- (get-p (eand e1 e2) hsh))))
                     (muthasheq)
                     (muthasheq e1 #f e2 #f)))]
    [(e1 . rst) (eor e1 (apply eor rst))]
    [es (let ([es (map ->pevt es)])
          (pevt (apply seteq es)
                (lambda (hsh)
                  (let loop ([ps '()] [hsh hsh] [es es])
                    (cond [(empty? es) (apply por (reverse ps))]
                          [else (let ([e (first es)])
                                  (loop (cons (get-p e hsh) ps)
                                        (hash-set hsh e #f)
                                        (rest es)))])))
                (muthasheq)
                (hash-copy (for/hasheq ([e (in-list es)])
                             (values e #f)))))]))

(define (eif*-proc ce te ee)
  (let ([ce (->pevt ce)] [te (->pevt te)] [ee (->pevt ee)])
    (pevt (lambda (hsh)
            (pif* (get-p ce hsh)
                  (get-p te (hash-set hsh ce #t))
                  (get-p ee (hash-set hsh ce #f))))
          (muthasheq)
          (muthasheq))))

(define eand eand-proc)
(define eor eor-proc)
(define eif* eif*-proc)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (define-check (check-e= actual expected)
    (let ([a (->pn (get-p actual (hasheq)))]
          [e (->pn (get-p expected (hasheq)))])
      (with-check-info*
       (list (make-check-actual a)
             (make-check-expected e))
       (lambda ()
         (check = a e)))))
  (define-check (check-e∆ actual expected ∆)
    (let ([a (->pn (get-p actual (hasheq)))]
          [b (->pn (get-p expected (hasheq)))])
      (with-check-info*
       (list (make-check-actual a)
             (make-check-expected b)
             (make-check-info '∆ ∆))
       (lambda ()
         (check-= a b ∆)))))
  (define-simple-macro (defre id:id ...)
    (begin (define id (->pevt (random))) ...))
  (define-simple-macro (rep body ...+)
    (for ([i (in-range 50)]) body ...))
  (test-case "get-p"
    (define e (->pevt 1/2))
    (check-equal? (get-p e (hasheq)) 1/2)
    (check-equal? (get-p e (hasheq e #t)) 1)
    (check-equal? (get-p e (hasheq e #f)) 0)
    (define e2
      (pevt (lambda (hsh)
              (match (get-p e hsh)
                [1 3/4] [0 5/7] [1/2 1/17]))
            (muthasheq)
            (muthasheq)))
    (check-equal? (get-p e2 (hasheq)) 1/17)
    (check-equal? (get-p e2 (hasheq e2 #t)) 1)
    (check-equal? (get-p e2 (hasheq e2 #f)) 0)
    (check-equal? (get-p e2 (hasheq e #t)) 3/4)
    (check-equal? (get-p e2 (hasheq e #f)) 5/7))
  (test-case "enot"
    (check-e= (enot 1) 0)
    (check-e= (enot 0) 1)
    (check-e= (enot 1/2) 1/2)
    (check-e= (enot 1/3) 2/3)
    (check-e= (enot 2/3) 1/3)
    (define e (->pevt 2/3))
    (define !e (enot e))
    (check-e= e 2/3)
    (check-e= !e 1/3)
    (check-e= (get-p !e (hasheq e #t)) 0)
    (check-e= (get-p !e (hasheq e #f)) 1)
    (check-e= (get-p !e (hasheq !e #t)) 1)
    (check-e= (get-p !e (hasheq !e #f)) 0)
    (check-e= (get-p e (hasheq !e #t)) 0)
    (check-e= (get-p e (hasheq !e #f)) 1))
  (test-case "eand"
    (check-e= (eand) 1)
    (check-e= (eand 1) 1)
    (check-e= (eand 0) 0)
    (check-e= (eand 1/2) 1/2)
    (check-e= (eand 2/3) 2/3)
    (check-e= (eand 1 1) 1)
    (check-e= (eand 0 0) 0)
    (check-e= (eand 1 0) 0)
    (check-e= (eand 0 1) 0)
    (check-e= (eand 1/2 1) 1/2)
    (check-e= (eand 1 1/2) 1/2)
    (check-e= (eand 1/2 1/2) 1/4)
    (define e (->pevt 1/2))
    (check-e= (eand e) 1/2)
    (check-e= (eand e e) 1/2)
    (check-e= (eand e e e e e e e) 1/2)
    (check-e= (eand e (enot e)) 0)
    (check-e= (eand (enot e) e) 0))
  (test-case "eor"
    (check-e= (eor) 0)
    (check-e= (eor 1) 1)
    (check-e= (eor 0) 0)
    (check-e= (eor 1/2) 1/2)
    (check-e= (eor 2/3) 2/3)
    (check-e= (eor 1 1) 1)
    (check-e= (eor 0 0) 0)
    (check-e= (eor 1 0) 1)
    (check-e= (eor 0 1) 1)
    (check-e= (eor 1/2 0) 1/2)
    (check-e= (eor 0 1/2) 1/2)
    (check-e= (eor 1/2 1/2) 3/4)
    (define e (->pevt 1/2))
    (check-e= (eor e) 1/2)
    (check-e= (eor e e) 1/2)
    (check-e= (eor e e e e e e e) 1/2)
    (check-e= (eor e (enot e)) 1)
    (check-e= (eor (enot e) e) 1))
  (test-case "(a || b) = !(!a && !b)"
    (rep
     (defre a b)
     (check-e∆ (eor a b) (enot (eand (enot a) (enot b))) 2.3e-16)
     (check-e∆ (eand a b) (enot (eor (enot a) (enot b))) 2.0e-16)))
  (test-case "eif*"
    (rep
     (defre e1 e2 e3)
     (check-e= (eif* 1 e1 e2) e1)
     (check-e= (eif* 0 e1 e2) e2)
     (check-e∆ (eif* e1 e2 e2) e2 1.2e-16)
     (check-e= (eif* e1 e2 0) (eand e1 e2))
     (check-e∆ (eif* e1 1 e2) (eor e1 e2) 2.3e-16)
     (check-e= (eif* e1 e2 e3)
               (let ([!e1 (enot e1)])
                 (eor (eand e1 e2)
                      (eand !e1 e3))))
     (check-e= (eif* e1 e1 0) e1)
     (check-e∆ (eif* e1 e1 e2) (eor e1 e2) 2.3e-16)
     (check-e= (eif* e1 0 e1) 0)
     (check-e= (eif* e1 1 e1) e1)
     (check-e= (eif* e1 e2 e1) (eand e1 e2))
     (check-e= (eif* e1 (enot e1) e1) 0)
     (check-e= (eif* e1 e1 (enot e1)) 1)
     (check-e= (eif* (enot e1) e1 (enot e1)) 0)
     (check-e= (eand e1 e2) (eif* e1 e2 0))
     (check-e∆ (eor e1 e2) (eif* e1 1 e2) 2.3e-16)
     (check-e= (enot e1) (eif* e1 0 1))
     (check-e= e1 (eif* e1 1 0)))
    (test-case "eif* thing"
      (define n 1e6)
      (define ∆ 1.6e-3)
      (rep
       (define e2 (->pevt (random))) (define e3 (->pevt (random)))
       (define e1->e2 (match (random 4)
                        [0 (hasheq e2 #t)]
                        [1 (hasheq e2 #f)] [_ (hasheq)]))
       (define e1->e3 (match (random 4)
                        [0 (hasheq e3 #t)]
                        [1 (hasheq e3 #f)] [_ (hasheq)]))
       (define e1.true-implies (hash-union e1->e2 e1->e3))
       (define !e1->e2 (match (random 4)
                         [0 (hasheq e2 #t)]
                         [1 (hasheq e2 #f)] [_ (hasheq)]))
       (define !e1->e3 (match (random 4)
                         [0 (hasheq e3 #t)]
                         [1 (hasheq e3 #f)] [_ (hasheq)]))
       (define e1.false-implies (hash-union !e1->e2 !e1->e3))
       (define p1 (random))
       (define e1 (pevt (lambda (hsh) p1) (hash-copy e1.true-implies) (hash-copy e1.false-implies)))
       (define p2 (get-p e2 (hasheq e1 #t)))
       (define p3 (get-p e3 (hasheq e1 #f)))
       (define p-if1then2else3
         (/ (for/sum ([i (in-range n)])
              (if (random-boolean/probability p1)
                  (if (random-boolean/probability p2) 1 0)
                  (if (random-boolean/probability p3) 1 0)))
            n))
       (check-e∆ (eif* e1 e2 e3) p-if1then2else3 ∆))))
  )
