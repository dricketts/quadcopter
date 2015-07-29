#lang racket

(require plot)

(define velocity -1)

(define epsilon 0.5)

(define initial
  (λ (x) (add1 (* -1 x))))

(define (next-function f t) 
  (λ (x) (+ (* -1 (f t) (- x t)) (f t))))
 
(define constant-interrupts
  (letrec ([go
            (lambda (a n)
              (if (= n 0)
                  a
                  (go (cons (+ epsilon (car a)) a)
                        (sub1 n))))])
    (reverse (go '(0) 10))))
                

(define (scan f init xs)
  (if (null? xs)
      '()
      (let ((v (f init (car xs))))
        (cons v
         (scan f v (cdr xs)))))) 
        
(define (random-interrupts)
  (let [(randoms 
         (let [(gen (make-pseudo-random-generator))]
           (for/list [(i 10)]
             (random gen))))]
    (scan + 0 (cons 0 randoms))))

(define (functions)
  (foldl (λ (x a) 
           (cons (next-function (car a) x)
                 a))
         (list initial)
         (random-interrupts)))

(define (graph)
  (plot (map (λ (f) (function f 0 5)) (functions))
        #:x-min 0 #:y-min 0
        #:x-label "time"	 
        #:y-label "x"))

(define (tests)
  (for/list [(i 10)]
    (graph)))