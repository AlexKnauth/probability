#lang racket

(provide probability-number?
         probability?
         ->pn
         pnot
         pand
         por
         pand-proc
         por-proc
         pand-expt
         por-expt
         pif
         pif*
         pif-proc
         pif*-proc
         probability->boolean
         random-boolean/probability
         )

(require syntax/parse/define
         my-cond
         (for-syntax racket/base
                     syntax/parse
                     racket/syntax
                     ))
(module+ test
  (require rackunit))

(define (probability-number? x)
  (and (real? x) (<= 0 x 1)))

(define (probability? x)
  (or (probability-number? x)
      (boolean? x)))

;; ->pn : Probability -> Probability-Number
(define (->pn x)
  (cond [(probability-number? x) x]
        [(boolean? x) (if x 1 0)]
        [else (error '->pn "expected probability?, given ~v" x)]))

(define (pnot p)
  (- 1 (->pn p)))

(define (pand-proc . args)
  (apply * (map ->pn args)))

(define (por-proc . args)
  (pnot (apply pand-proc (map pnot args))))

(define (pand-expt p n)
  (expt (->pn p) n))

(define (por-expt p n)
  (pnot (expt (pnot p) n)))

(define (pif-proc cp then else)
  (if (probability->boolean cp)
      then
      else))

(define (pif*-proc cp tp ep)
  (let ([cp (->pn cp)])
    (cond [(= cp 1) (->pn tp)]
          [(= cp 0) (->pn ep)]
          [else
           (pif*-proc-ish cp (->pn tp) (->pn ep))])))

(define (pif*-proc-ish cp tp ep)
  (let* ([cp (->pn cp)] [tp (->pn tp)] [ep (->pn ep)] [!cp (->pn (pnot cp))])
    ;#;#;[]
    (/ (+ (* cp tp) (* !cp ep))
       (+ cp !cp))
    #;#;[]
    (por (pand cp tp)
         (pand !cp ep))
    ))

(begin-for-syntax
  (define-syntax-class p-expr
    [pattern (~var p (expr/c #'probability? #:name "probability argument" #:context this-syntax))
             #:with norm (syntax/loc #'p (->pn p.c))])
  
  (define (parse-pand-exprs exprs pre-ids)
    (syntax-parse exprs
      [() (parse-pand-pre-ids pre-ids)]
      [(p1:expr . rst)
       #:with p1-id (generate-temporary #'p)
       #:with rst-norm (parse-pand-exprs #'rst #`(p1-id . #,pre-ids))
       #`(let ([p1-id p1])
           (if (zero? p1-id) 0
               rst-norm))]))
  
  (define (parse-pand-pre-ids pre-ids)
    (syntax-parse pre-ids
      [() #'1]
      [(id:id) #'id]
      [(id:id ...) #'(* id ...)])))

(define-syntax pand
  (syntax-parser
    [(pand) #'1]
    [(pand p:p-expr) #'p.norm]
    [(pand p:p-expr ...) 
     (parse-pand-exprs #'(p.norm ...) #'())]
    [pand:id (syntax/loc #'pand pand-proc)]))

(define-syntax por
  (syntax-parser
    [(por) #'0]
    [(por p:p-expr) #'p.norm]
    [(por p:p-expr ...)
     #:with (!p ...) (for/list ([p (in-list (syntax->list #'(p.norm ...)))])
                       (with-syntax ([p p])
                         #'(pnot p)))
     #:with !r (parse-pand-exprs #'(!p ...) #'())
     #'(pnot !r)]
    [por:id (syntax/loc #'por por-proc)]))

(define-syntax pif
  (syntax-parser
    [(pif p then else)
     #'(if (probability->boolean p)
           then
           else)]
    [pif:id (syntax/loc #'pif pif-proc)]))

(define-syntax pif*
  (syntax-parser
    [(pif* condition-p:p-expr then-p:p-expr else-p:p-expr)
     #'(let ([cp condition-p.norm])
         (cond [(= cp 1) then-p.norm]
               [(= cp 0) else-p.norm]
               [else
                (let ([tp then-p.norm] [ep else-p.norm])
                  (pif*-proc-ish cp tp ep))]))]
    [ppif:id (syntax/loc #'ppif pif*-proc)]))

(define (probability->boolean p)
  (let ([p (->pn p)])
    (match p [1 #t] [0 #f]
      [_ (error 'probability->boolean "given: ~v" p)])))

(define (random-boolean/probability p)
  (let ([p (->pn p)])
    (match p [1 #t] [0 #f]
      [_ (let ([r (random)])
           (< r p))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(module+ test
  (define-check (check-p= actual expected)
    (check-equal? (->pn actual) (->pn expected)))
  (define-check (check-p∆ actual expected ∆)
    (check-= (->pn actual) (->pn expected) ∆))
  (define-simple-macro (defrp id:id ...)
    (begin (define id (random)) ...))
  (define-simple-macro (rep body ...+)
    (for ([i (in-range 50)]) body ...))
  (test-case "pnot"
    (check-p= (pnot 1) 0)
    (check-p= (pnot 0) 1)
    (check-p= (pnot 1/2) 1/2)
    (check-p= (pnot 1/3) 2/3)
    (check-p= (pnot 2/3) 1/3))
  (test-case "pand"
    (check-p= (pand) 1)
    (rep
     (defrp p)
     (check-p= (pand p) p)
     (check-p= (pand p 1) p)
     (check-p= (pand 1 p) p))
    (check-p= (pand 1 1) 1)
    (check-p= (pand 0 1) 0)
    (check-p= (pand 1 0) 0)
    (check-p= (pand 1/2 1) 1/2)
    (check-p= (pand 1 1/2) 1/2)
    (check-p= (pand 1/2 1/2) 1/4)
    (check-p= (pand 1/2 1/3) 1/6)
    (check-p= (pand 1/12 1/5) 1/60)
    (check-p= (pand-expt 1 2) 1)
    (check-p= (pand-expt 1/2 2) 1/4)
    (check-p= (pand-expt 1/2 3) 1/8)
    (check-p= (pand-expt 1/3 2) 1/9))
  (test-case "por"
    (check-p= (por) 0)
    (rep
     (defrp p p1 p2)
     (check-p∆ (por p) p 1.2e-16)
     (check-p∆ (por p 0) p 1.2e-16)
     (check-p∆ (por 0 p) p 1.2e-16)
     (check-p∆ (por p1 p2) (+ p1 (- p2 (pand p1 p2))) 1.6e-16))
    (check-p= (por 1 1) 1)
    (check-p= (por 0 0) 0)
    (check-p= (por 1 0) 1)
    (check-p= (por 0 1) 1)
    (check-p= (por 1/2 0) 1/2)
    (check-p= (por 1/2 1/2) 3/4)
    (check-p= (por 1/3 1/3) 5/9) ; (+ 1/3 (* 2/3 1/3))
    (check-p= (por-expt 1/2 2) 3/4)
    (check-p= (por-expt 1/2 3) 7/8)
    (check-p= (por-expt 1/2 4) 15/16)
    (check-p= (por-expt 1/2 10) 1023/1024)
    (check-p= (por-expt 1/3 0) 0)
    (check-p= (por-expt 1/3 1) 1/3)   ; (+ 0 (* 1 1/3))
    (check-p= (por-expt 1/3 2) 5/9)   ; (+ 1/3 (* 2/3 1/3))
    (check-p= (por-expt 1/3 3) 19/27) ; (+ 5/9 (* 4/9 1/3))
    (check-p= (por-expt 1/3 4) 65/81) ; (+ 19/27 (* 8/27 1/3))
    )
  (test-case "random-boolean/probability"
    (define n 1e5)
    (define ∆ 1e-2)
    (rep
     (defrp p)
     (check-p∆ (/ (for/sum ([i (in-range n)])
                    (if (random-boolean/probability p) 1 0))
                  n)
               p
               ∆)))
  (test-case "pif*"
    (rep
     (defrp p1 p2 p3)
     (check-p= (pif* 1 p1 p2) p1)
     (check-p= (pif* 0 p1 p2) p2)
     (check-p∆ (pif* p1 p2 p2) p2 1.2e-16)
     (check-p= (pif* p1 p2 0) (pand p1 p2))
     (check-p∆ (pif* p1 1 p2) (por p1 p2) 2.3e-16)
     ;(check-p= (ppif p1 p2 1) (por (pand p1 p2) (pand (pnot p1) 1)))
     ;(check-p= (ppif p1 p2 p3) (por (pand p1 p2) (pand (pnot p1) p3)))
     )
    (check-p= (pif* 1/2 1 0) 1/2)
    (check-p= (pif* 2/3 1 0) 2/3)
    (check-p= (pif* 2/3 0 1) 1/3)
    (check-p= (pif* 1/2 0 0) 0)
    (check-p= (pif* 1/2 1 1) 1)
    (check-p= (pif* 1/2 1 1/2) 3/4)
    (check-p= (pif* 1/2 0 1/2) 1/4)
    (check-p= (pif* 2/3 1/2 0) 1/3)
    (test-case "pif* thing"
      (define n 4e5)
      (define ∆ 3e-3)
      (rep
       (defrp p1 p2 p3)
       (define p-if1then2else3
         (/ (for/sum ([i (in-range n)])
              (if (random-boolean/probability p1)
                  (if (random-boolean/probability p2) 1 0)
                  (if (random-boolean/probability p3) 1 0)))
            n))
       (check-p∆ (pif* p1 p2 p3) p-if1then2else3 ∆)))
    ))
