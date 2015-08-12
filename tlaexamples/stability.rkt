#lang racket

(require plot)

(define velocity -1)

(define epsilon 0.5)

(define initial
  (λ (x) (+ 1 (* -1 x))))

(define (next-function f x1) 
  (let* ((y1 (f x1))
         (x2 (+ 1 x1))
         (y2 0)
         (m  (/ (- y2 y1) (- x2 x1))))
    (λ (x) (+ y1 (* m (- x x1))))))

  ;  (λ (x) (+ (* -1 y1 (- x x1)) y1))))


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
         constant-interrupts))

; |b| must be <= 1
(define exp-decay
  (lambda (t)
    (let ((t0 0)
          (x0 1)
          (a 1)
          (b -1))
      (* x0 a (exp (* b (- t t0)))))))

(define (graph) 
  (let ((fxs (functions)))
    
  (plot 
   
   (map (λ (f) (function (min-fx exp-decay f) 0 5)) fxs)
  ; (cons 
   ; (function exp-decay 0 5 #:color 15)
    ;(map (λ (f) (function f 0 5)) (functions)))
   
   #:x-min 0 #:y-min 0
   #:x-max 5 #:y-max 2
   #:x-label "time"	 
   #:y-label "x")))

(define (diff f g)
  (λ (t) (- (f t) (g t))))

(define (min-fx f g)
  (λ (t) (min (f t) (g t))))


(define (tests)
  (for/list [(i 10)]
    (graph)))

;(tests)
