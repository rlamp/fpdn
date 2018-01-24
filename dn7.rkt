#lang racket

(define (power x n)
  (if (= n 0)
    1
    (* x (power x (- n 1)))
  )
)

(define (gcd a b)
	(if (= 0 b)
		a
  	(gcd b (modulo a b))
 )
)

(define (fib a)
 (cond
   [(< a 3) 1]
   [(= a 3) 2]
   [#t (+ (fib (- a 1)) (fib (- a 2)))]
  )
)

(define (reverse xs)
	(if (null? xs)
		null
  	(append (reverse (cdr xs)) (list (car xs)))
  )
)

(define (remove x xs)
  (cond
    [(null? xs) null]
		[(= x (car xs)) (remove x (cdr xs))]
    [#t (append (list (car xs)) (remove x (cdr xs)))]
	)
)

(define (map f xs)
	(if (null? xs)
		null
 		(append (list (f (car xs))) (map f (cdr xs)) )	
   )
)

(define (filter f xs)
	(if (null? xs)
     null
     (if (f (car xs))
         (append (list (car xs)) (filter f (cdr xs)) )
         (filter f (cdr xs))
      )
  )
)

(define (zip xs1 xs2) 
  (if (or (null? xs1) (null? xs2))
      null
      (append (list (cons (car xs1) (car xs2))) (zip (cdr xs1) (cdr xs2)) )
    )
)

(define (range from to k)
	(if (<= from to)
   	 (append (list from) (range (+ from k) to k ) )
     null
   )
)

(define (everynth_aux n ctr xs)
	(cond
 		[(null? xs) null ]
   	[(= ctr 1) (append (list (car xs)) (everynth_aux n n (cdr xs) ) ) ]
   	[#t (everynth_aux n (- ctr 1) (cdr xs) ) ]
   )
)

(define (everynth n xs) (everynth_aux n n xs) )


; tests
; ( = (power 2 3) 8 )
; ( = (gcd 7 3) 1 )
; ( = (fib 3) 2 )
; ( equal? (reverse (list 1 2 3)) (list 3 2 1) )
; ( equal? (remove 3 (list 1 2 3 4 5 4 3 2 1)) (list 1 2 4 5 4 2 1) )
; ( equal? (map (lambda (a) (* a 2)) (list 1 2 3)) (list 2 4 6) )
; ( equal? (filter (lambda (a) (= (modulo a 2) 0)) (list 1 2 3)) (list 2) )
; ( equal? (zip (list 1 2 3) (list 4 5 6)) (list (cons 1 4) (cons 2 5) (cons 3 6)) )
; ( equal? (range 1 3 1) (list 1 2 3) )
; ( equal? (everynth 3 (list 1 2 3 4 5 4 3 2 1 2)) (list 3 4 1) )
