#lang racket

(define ones (cons 1 (lambda () ones)))

(define naturals
  (letrec
      ([f (lambda (x) (cons x (lambda () ( f (+ x 1)) )))])
    (f 1)
    ))

(define fibs
  (letrec
      ([f (lambda (x y) (cons x (lambda () (f y (+ x y)))))])
    (f 1 1)
    )
  )


(define (first n tok)
  (letrec
      ([f (lambda (n tok acc) (
                               if (= n 0)
                                  acc
                                  (f (- n 1) ((cdr tok)) (append acc (list (car tok))))))])
    (f n tok null))) 


(define (squares tok)
  (cons (expt (car tok) 2)  (lambda () (squares ((cdr tok))))))


(define (my-delay thunk)
  (mcons 0 (mcons thunk "result_placeholder")))

(define (my-force promise)
  (cond
    [(= (mcar promise) 0) (begin
                            (set-mcdr! promise (mcons (mcar (mcdr promise)) ((mcar (mcdr promise)))))
                            (set-mcar! promise 4)
                            (mcdr (mcdr promise)))]
    [#t (begin
          (set-mcar! promise (- (mcar promise) 1))
          (mcdr (mcdr promise)))]))


(define-syntax sml
  (syntax-rules (:: hd tl null nil)
    [(sml nil) null]
    [(sml null xs) (null? xs)]
    [(sml tl xs) (cdr xs)]
    [(sml hd xs) (car xs)]
    [(sml x :: xs) (cons x xs)]))


(define (partitions k n)
  (- n k))



; (car ones)

; (car ((cdr ((cdr ones)))))

; (car naturals)

; (car ((cdr ((cdr naturals)))))

;(car fibs)

;(car ((cdr fibs)))

;(car ((cdr ((cdr fibs)))))

;(car ((cdr ((cdr ((cdr fibs)))))))

;(car ((cdr ((cdr ((cdr ((cdr fibs)))))))))

;(car ((cdr ((cdr ((cdr ((cdr ((cdr fibs)))))))))))

;(first 22 ones)

;(first 22 naturals)

;(first 22 fibs)

;(first 22 (squares ones))

;(first 22 (squares naturals))

;(first 22 (squares fibs))

;(define f (my-delay (lambda () (begin (write "bla") 123))))

;(my-force f)

;(my-force f)

;(my-force f)

;(my-force f)

;(my-force f)

;(my-force f)

;(my-force f)

;(sml nil)

;(sml null (sml nil))

;(sml hd (sml 5 :: null))

;(sml tl (sml 5 :: (sml 4 :: (sml nil))))

;(sml 5 :: (sml 4 :: (sml nil)))

;(partitions 3 7)