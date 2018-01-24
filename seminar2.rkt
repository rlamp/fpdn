#lang racket

; podatkovni tipi
(struct int (n) #:transparent)
(struct true () #:transparent)
(struct false () #:transparent)
(struct complex (a b) #:transparent)
(struct :: (e1 e2) #:transparent)
(struct empty () #:transparent)

; nadzor toka
(struct if-then-else (condition e1 e2) #:transparent)
(struct is-int (e1) #:transparent)
(struct is-bool (e1) #:transparent)
(struct is-complex (e1) #:transparent)
(struct is-list (e1) #:transparent)
(struct add (e1 e2) #:transparent)
(struct mul (e1 e2) #:transparent)
(struct gt (e1 e2) #:transparent)
(struct both (e1 e2) #:transparent)
(struct any (e1 e2) #:transparent)
(struct ! (e1) #:transparent)
(struct hd (x) #:transparent) 
(struct tl (x) #:transparent) 
(struct is-empty (x) #:transparent) 
(struct @ (a b) #:transparent) 
(struct real (e1) #:transparent) 
(struct imaginary (e1) #:transparent)

; spremenljivke
(struct var (s e1 e2) #:transparent)
(struct valof (s) #:transparent)

; funkcije
(struct fun (name fargs body) #:transparent)
(struct proc (name body) #:transparent)
(struct envelope (env f) #:transparent)
(struct call (e args) #:transparent)

; helper functions
(define (milist_to_list ls)
  (cond
    [(empty? ls) null]
    [(::? ls) (cons (::-e1 ls) (milist_to_list (::-e2 ls)))]
    [#t (list ls)]))

(define (append_list_to_milist ls mls)
  (foldr (lambda (v l) (:: v l)) mls ls))

(define zip (lambda (l1 l2) (map cons l1 l2)))

(define (optimise_env env newenv)
  (cond
    [(null? env) newenv]
    [#t (letrec ([head (car env)]
                 [tail (cdr env)]
                 [newtail (filter (lambda (x) (not (equal? (car x) (car head)))) tail)]
                 [ne (append newenv (list head))])
          (optimise_env newtail ne))]))

(define (remove_fargs env fargs)
  (filter (lambda (x) (foldl (lambda (y a)  (and a (not (equal? y (car x))))) #t fargs)) env))
        
; macros
[define (to-complex e1)
  (complex e1 (int 0))]

[define (conj e1)
  (var "_CMPLX_NMBR_" e1 (complex (real (valof "_CMPLX_NMBR_")) (mul (int -1) (imaginary (valof "_CMPLX_NMBR_")))))]

[define (~ e1)
  (mul (int -1) e1)]

[define (lt e1 e2)
  ;(var "_EXP_1_" e1 (var "_EXP_2_" e2 (gt (valof "_EXP_2_") (valof "_EXP_1_"))))]
  (gt e2 e1)]

[define (same e1 e2)
  (var "_EXP_1_" e1 (var "_EXP_2_" e2 (! (any (gt (valof "_EXP_1_") (valof "_EXP_2_")) (gt (valof "_EXP_2_") (valof "_EXP_1_"))))))]

; main fucntion
(define (mi izraz okolje)
  (letrec ([mii (lambda (e env)
                  (cond
                    [(int? e) e]
                    [(true? e) e]
                    [(false? e) e]
                    [(complex? e) (complex (mii (complex-a e) env) (mii (complex-b e) env))]
                    [(::? e) (:: (mii (::-e1 e) env) (mii (::-e2 e) env))]
                    [(empty? e) e]
                    
                    [(if-then-else? e) (let ([pogoj (mii (if-then-else-condition e) env)])
                                         (cond
                                           [(true? pogoj) (mii (if-then-else-e1 e) env)]
                                           [(false? pogoj) (mii (if-then-else-e2 e) env)]
                                           [#t (error "if-then-else: bad condition")]))]
                    [(is-int? e) (if (int? (mii (is-int-e1 e) env)) (true) (false))]
                    [(is-bool? e) (let ([val (mii (is-bool-e1 e) env)]) (if (or (true? val) (false? val)) (true) (false)))]
                    [(is-complex? e) (if (complex? (mii (is-complex-e1 e) env)) (true) (false))]
                    [(is-list? e) (let ([ee (mii (is-list-e1 e) env)]) (if (or (::? ee) (empty? ee)) (true) (false)))]

                    [(add? e) (let ([val_e1 (mii (add-e1 e) env)] [val_e2 (mii (add-e2 e) env)])
                                (cond
                                  [(and (int? val_e1) (int? val_e2)) (int (+ (int-n val_e1) (int-n val_e2)))]
                                  [(and (complex? val_e1) (complex? val_e2)) (complex (int (+ (int-n (complex-a val_e1)) (int-n (complex-a val_e2)))) (int (+ (int-n (complex-b val_e1)) (int-n (complex-b val_e2)))))]
                                  [#t (error "add: supported only for int and complex ->" val_e1 val_e2)]))]
                    
                    [(mul? e) (let ([val_e1 (mii (mul-e1 e) env)] [val_e2 (mii (mul-e2 e) env)])
                                (cond
                                  [(and (int? val_e1) (int? val_e2)) (int (* (int-n val_e1) (int-n val_e2)))]
                                  [(and (complex? val_e1) (complex? val_e2)) (complex (int (- (* (int-n (complex-a val_e1)) (int-n (complex-a val_e2))) (* (int-n (complex-b val_e1)) (int-n (complex-b val_e2)))))
                                                                                      (int (+ (* (int-n (complex-a val_e1)) (int-n (complex-b val_e2))) (* (int-n (complex-b val_e1)) (int-n (complex-a val_e2))))))]
                                  [#t (error "mul: supported only for int and complex ->" val_e1 val_e2)]))]
                    [(gt? e) (let ([val_e1 (mii (gt-e1 e) env)]
                                   [val_e2 (mii (gt-e2 e) env)])
                               (if (and (int? val_e1) (int? val_e2))
                                   (if (> (int-n val_e1) (int-n val_e2)) (true) (false))
                                   (error "gt: only supported for int ->" val_e1 val_e2)))]

                    [(both? e) (let ([val_e1 (mii (both-e1 e) env)] [val_e2 (mii (both-e2 e) env)])
                                 (if (and (or (true? val_e1) (false? val_e1)) (or (true? val_e2) (false? val_e2)))
                                     (if (and (true? val_e1) (true? val_e2))
                                         (true)
                                         (false))
                                     (error "both: define only for bool ->" val_e1 val_e2)))]
                    
                    [(any? e) (let ([val_e1 (mii (any-e1 e) env)] [val_e2 (mii (any-e2 e) env)])
                                (if (and (or (true? val_e1) (false? val_e1)) (or (true? val_e2) (false? val_e2)))
                                    (if (or (true? val_e1) (true? val_e2))
                                        (true)
                                        (false))
                                    (error "any: define only for bool ->" val_e1 val_e2)))]
                    
                    [(!? e) (let ([val_e1 (mii (!-e1 e) env)])
                              (cond
                                [(true? val_e1) (false)]
                                [(false? val_e1) (true)]
                                [#t (error "!: defined only for bool ->" val_e1)]))]

                    [(hd? e) (let ([ls (mii (hd-x e) env)])
                               (if (::? ls)
                                   (::-e1 ls)
                                   (error "hd: defined only for list ->" ls)))]
                    
                    [(tl? e) (let ([ls (mii (tl-x e) env)])
                               (if (::? ls)
                                   (::-e2 ls)
                                   (error "tl: defined only for list ->" ls)))]
                    
                    [(is-empty? e) (let ([ls (mii (is-empty-x e) env)])
                                     (if (empty? ls)
                                         (true)
                                         (if (::? ls)
                                             (false)
                                             (error "is-empty: defined only for list ->" ls))))]
                    
                    [(@? e) (let ([ea (mii (@-a e) env)]
                                  [eb (mii (@-b e) env)])
                              (cond
                                [(and (empty? ea) (empty? eb)) (empty)]
                                [(and (::? ea) (empty? eb)) ea]
                                [(and (empty? ea) (::? eb)) eb]
                                [(and (::? ea) (::? eb))
                                 (let ([ls (milist_to_list ea)]) (append_list_to_milist ls eb))]
                                [#t (error "@: defined only for lists ->" ea eb)]))]
                              
                    [(real? e) (let ([val_e1 (mii (real-e1 e) env)])
                                 (if (complex? val_e1)
                                     (complex-a val_e1)
                                     (error "real: defined only for complex ->" val_e1)))]
                    
                    [(imaginary? e) (let ([val_e1 (mii (imaginary-e1 e) env)])
                                      (if (complex? val_e1)
                                          (complex-b val_e1)
                                          (error "imaginary: defined only for complex ->" val_e1)))]

                    [(var? e) (mii (var-e2 e) (cons (cons (var-s e) (mii (var-e1 e) env)) env))]
                    [(valof? e) (let ([val (assoc (valof-s e) env)])
                                  (if val
                                      (cdr val)
                                      (error "valof: no such variable ->" (valof-s e))))]

                    [(fun? e) (cond
                                [(check-duplicates (fun-fargs e)) (error "fun: names of arguments must be unique ->" (fun-fargs e))]
                                [(not (string? (fun-name e))) (error "fun: name of function must be a string ->" (fun-name e))]
                                [#t (envelope (remove_fargs (optimise_env env null) (cons (fun-name e) (fun-fargs e))) e)])]
                    [(proc? e) e]
                    [(call? e) (let ([ee (mii (call-e e) env)])
                                 (cond
                                   [(proc? ee) (mii (proc-body ee) (cons (cons (proc-name ee) ee) env))]
                                   [(envelope? ee) (let ([fbody (fun-body (envelope-f ee))]
                                                         [fargs (fun-fargs (envelope-f ee))]
                                                         [fname (fun-name (envelope-f ee))]
                                                         [envenv (envelope-env ee)])
                                                     (mii fbody (optimise_env (append (zip fargs (map (lambda (x) (mii x env)) (call-args e))) (cons (cons fname ee) envenv)) null)))]
                                   [#t (error "call: defined only for proc and fun ->" ee)]))]
                    
                    [#t (error "mii: invalid expression ->" e)]
                    ))])
    (mii izraz okolje)))



;; TESTS
;; podatkovni tipi
;
;(equal? (mi (int 1) null) (int 1))
;(equal? (mi (int 2) null) (int 2))
;(equal? (mi (int -3) null) (int -3))
;(equal? (mi (true) null) (true))
;(equal? (mi (false)  null) (false))
;(equal? (mi (complex (int 1) (int 2)) null) (complex (int 1) (int 2)))
;(equal? (empty) (empty))
;(equal? (mi (:: (int 3) (:: (int 2) (:: (int 1) (empty)))) null) (:: (int 3) (:: (int 2) (:: (int 1) (empty)))))
;(equal? (mi (:: (int 3) (:: (int 2) (:: (int 1) (complex (int 1) (int 2))))) null) (:: (int 3) (:: (int 2) (:: (int 1) (complex (int 1) (int 2))))))
;
;; vejitev
;
;(equal? (mi (if-then-else (true) (int 1) (int 0)) null) (int 1))
;(equal? (mi (if-then-else (false) (int 1) (int 0)) null) (int 0))
;(equal? (mi (if-then-else (true) (if-then-else (true) (int 1) (int 2)) (int 0)) null) (int 1))
;(equal? (mi (if-then-else (true) (if-then-else (false) (int 1) (int 2)) (int 0)) null) (int 2))
;(equal? (mi (if-then-else (false) (if-then-else (false) (int 1) (int 2)) (int 0)) null) (int 0))
;
;; preverjanje tipov
;
;(equal? (mi (is-int (int 2)) null) (true))
;(equal? (mi (is-int (true)) null) (false))
;(equal? (mi (is-bool (true)) null) (true))
;(equal? (mi (is-bool (false)) null) (true))
;(equal? (mi (is-bool (int 2)) null) (false))
;(equal? (mi (is-complex (int 2)) null) (false))
;(equal? (mi (is-complex (complex (int 1) (int 2))) null) (true))
;(equal? (mi (is-list (empty)) null) (true))
;(equal? (mi (is-list (:: (int 1) (:: (int 2) (int 3)))) null) (true))
;
;; aritmeticne operacije
;
;(equal? (mi (add (int 1) (int 1)) null) (int 2))
;(equal? (mi (add (int 1) (int 2)) null) (int 3))
;(equal? (mi (add (int 1) (int -1)) null) (int 0))
;(equal? (mi (add (int 1) (add (int 0) (int 0))) null) (int 1))
;(equal? (mi (add (add (int 0) (int 0)) (add (int 0) (int 0))) null) (int 0))
;(equal? (mi (mul (int 1) (int 1)) null) (int 1))
;(equal? (mi (mul (int 1) (int 2)) null) (int 2))
;(equal? (mi (mul (int 1) (int -1)) null) (int -1))
;(equal? (mi (mul (int 1) (add (int 0) (int 0))) null) (int 0))
;(equal? (mi (mul (mul (int 0) (int 0)) (add (int 0) (int 0))) null) (int 0))
;(equal? (mi (add (complex (int 1) (int 1)) (complex (int 1) (int 1))) null) (complex (int 2) (int 2)))
;(equal? (mi (add (complex (int -2) (int 3)) (complex (int 3) (int 2))) null) (complex (int 1) (int 5)))
;(equal? (mi (mul (complex (int 1) (int 4)) (complex (int 5) (int 1))) null) (complex (int 1) (int 21)))
;(equal? (mi (mul (complex (int 4) (int -3)) (complex (int 2) (int 5))) null) (complex (int 23) (int 14)))
;(equal? (mi (mul (complex (int 7) (int -9)) (complex (int 4) (int -6))) null) (complex (int -26) (int -78)))
;(equal? (mi (gt (int 1) (int 2)) null) (false))
;(equal? (mi (gt (int 2) (int 1)) null) (true))
;(equal? (mi (gt (int 2) (int 2)) null) (false))
;
;; logicne operacije
;
;(equal? (mi (both (true) (true)) null) (true))
;(equal? (mi (both (true) (false)) null) (false))
;(equal? (mi (both (false) (true)) null) (false))
;(equal? (mi (both (false) (false)) null) (false))
;(equal? (mi (any (true) (true)) null) (true))
;(equal? (mi (any (true) (false)) null) (true))
;(equal? (mi (any (false) (true)) null) (true))
;(equal? (mi (any (false) (false)) null) (false))
;(equal? (mi (! (true)) null) (false))
;(equal? (mi (! (false)) null) (true))
;(equal? (mi (any (both (true) (! (false))) (! (! (! (gt (int 2) (int 1)))))) null) (true))
;(equal? (mi (both (both (true) (! (false))) (! (! (! (gt (int 2) (int 1)))))) null) (false))
;
;; operacije nad seznami
;
;(equal? (mi (hd (:: (int 1) (:: (int 2) (int 3)))) null) (int 1))
;(equal? (mi (tl (:: (int 1) (:: (int 2) (int 3)))) null) (:: (int 2) (int 3)))
;(equal? (mi (hd (:: (int 1) (empty))) null) (int 1))
;(equal? (mi (tl (:: (int 1) (empty))) null) (empty))
;(equal? (mi (is-empty (empty)) null) (true))
;(equal? (mi (is-empty (:: (int 1) (empty))) null) (false))
;(equal? (mi (@ (:: (int 1) (:: (int 2) (int 3))) (:: (int 4) (empty))) null) (:: (int 1) (:: (int 2) (:: (int 3) (:: (int 4) (empty))))))
;(equal? (mi (@ (:: (int 1) (:: (int 2) (empty))) (:: (int 3) (int 4))) null) (:: (int 1) (:: (int 2) (:: (int 3) (int 4)))))
;
;; kompleksna stevila
;
;(equal? (mi (real (complex (int 1) (int 2))) null) (int 1))
;(equal? (mi (imaginary (complex (int 1) (int 2))) null) (int 2))
;(equal? (mi (real (add (complex (int 1) (int 2)) (complex (int 1) (int 0)))) null) (int 2))
;(equal? (mi (imaginary (add (complex (int 1) (int 2)) (complex (int 1) (int 0)))) null) (int 2))
;
;; spremenljivke
;
;(equal? (mi (var "x" (int 2) (valof "x")) null) (int 2))
;(equal? (mi (var "x" (int 2) (var "x" (int 3) (valof "x"))) null) (int 3))
;(equal? (mi (var "x" (int 2) (var "y" (int 3) (add (valof "x") (valof "y")))) null) (int 5))
;
;; funkcije
;
;(define add1 (fun "add1" (list "x") (add (valof "x") (int 1))))
;(equal? (mi (call add1 (list (int 5))) null) (int 6))
;(equal? (mi (call add1 (list (int 1))) null) (int 2))
;(define add2 (fun "add1" (list "x") (if-then-else (gt (valof "x") (int 10)) (valof "x") (add (valof "x") (int 10)))))
;(equal? (mi (call add2 (list (int 1))) null) (int 11))
;(equal? (mi (call add2 (list (int 10))) null) (int 20))
;(equal? (mi (call add2 (list (int 12))) null) (int 12))
;(define prc (proc "prc" (int 1)))
;(define prc2 (proc "prc" (valof "x")))
;(equal? (mi (call prc null) null) (int 1))
;(equal? (mi (call prc2 null) (list (cons "x" (int 100)))) (int 100))
;
;(define addtoten (fun "addto10" (list "x") (if-then-else (gt (valof "x") (int 10)) (valof "x") (call (valof "addto10") (list (add (valof "x") (int 1)))))))
;(equal? (mi (call addtoten (list (int 10))) null) (int 11))
;
;(define addtotenp (proc "addto10" (if-then-else (gt (valof "x") (int 9)) (valof "x") (var "x" (add (valof "x") (int 1)) (call (valof "addto10") null)))))
;(equal? (mi (call addtotenp null) (list (cons "x" (int 2)))) (int 10))
;(equal? (mi (call addtotenp null) (list (cons "x" (int 100)))) (int 100))
;
;(define fib (fun "fib" (list "n")
;                 (if-then-else (gt (int 3) (valof "n"))
;                               (int 1)
;                               (add (call (valof "fib") (list (add (valof "n") (int -1))))
;                                    (call (valof "fib") (list (add (valof "n") (int -2))))))))
;(equal? (mi (call fib (list (int 1))) null) (int 1))
;(equal? (mi (call fib (list (int 2))) null) (int 1))
;(equal? (mi (call fib (list (int 3))) null) (int 2))
;(equal? (mi (call fib (list (int 4))) null) (int 3))
;(equal? (mi (call fib (list (int 5))) null) (int 5))
;(equal? (mi (call fib (list (int 6))) null) (int 8))
;(equal? (mi (call fib (list (int 7))) null) (int 13))
;(equal? (mi (call fib (list (int 8))) null) (int 21))
;(equal? (mi (call fib (list (int 9))) null) (int 34))
;(equal? (mi (call fib (list (int 10))) null) (int 55))
;
;(define reverse (fun "reverse" (list "xs")
;                     (if-then-else
;                      (is-empty (valof "xs"))
;                      (empty)
;                      (@ (call (valof "reverse") (list (tl (valof "xs"))))
;                         (:: (hd (valof "xs")) (empty))))))
;
;(equal? (mi (call reverse (list (:: (int 5) (:: (int 4) (:: (int 3) (empty)))))) null) (:: (int 3) (:: (int 4) (:: (int 5) (empty)))))
;(equal? (mi (call reverse (list (empty))) null) (empty))
;(equal? (mi (call reverse (list (:: (int 3) (empty)))) null) (:: (int 3) (empty)))
;
;(define tail-reverse (fun "tail-reverse" (list "xs")
;                          (var "aux" (fun "aux" (list "xs" "acc")
;                                          (if-then-else
;                                           (is-empty (valof "xs"))
;                                           (valof "acc")
;                                           (call (valof "aux") (list (tl (valof "xs")) (:: (hd (valof "xs")) (valof "acc"))))))
;                               (call (valof "aux") (list (valof "xs") (empty))))))
;
;(equal? (mi (call tail-reverse (list (:: (int 5) (:: (int 4) (:: (int 3) (empty)))))) null) (:: (int 3) (:: (int 4) (:: (int 5) (empty)))))
;(equal? (mi (call tail-reverse (list (empty))) null) (empty))
;(equal? (mi (call tail-reverse (list (:: (int 3) (empty)))) null) (:: (int 3) (empty)))
;
;; makri
;
;(equal? (mi (to-complex (add (int 1) (int 2))) null) (complex (int 3) (int 0)))
;(equal? (mi (conj (complex (int 4) (int 2))) null) (complex (int 4) (int -2)))
;(equal? (mi (~ (int 2)) null) (int -2))
;(equal? (mi (lt (int 2) (int 3)) null) (true))
;(equal? (mi (lt (int 2) (int 2)) null) (false))
;(equal? (mi (lt (int 3) (int 2)) null) (false))
;(equal? (mi (same (int 2) (int 3)) null) (false))
;(equal? (mi (same (int 2) (int 2)) null) (true))
;(equal? (mi (same (int 3) (int 2)) null) (false))