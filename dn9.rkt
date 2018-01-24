#lang racket

; podatkovni tipi
(struct int (n) #:transparent)
(struct true () #:transparent)
(struct false () #:transparent)

; nadzor toka
(struct if-then-else (condition e1 e2) #:transparent)
(struct is-int (e1) #:transparent)
(struct is-bool (e1) #:transparent)
(struct add (e1 e2) #:transparent)
(struct gt (e1 e2) #:transparent)
(struct both (e1 e2) #:transparent)
(struct ! (e1) #:transparent)

; spremenljivke
(struct var (s e1 e2) #:transparent)
(struct valof (s) #:transparent)

; funkcije
(struct fun (name fargs body) #:transparent)
(struct proc (name body) #:transparent)
(struct envelope (env f) #:transparent)
(struct call (e args) #:transparent)


; macros
(define-syntax lt
  (syntax-rules ()
    [(lt e1 e2)
     (gt e2 e1)]))

(define-syntax ifte
  (syntax-rules (then else)
    [(ifte cnd then e1 else e2)
     (if-then-else cnd e1 e2)]))


; main fucntion
(define (mi izraz)
  (letrec ([mii (lambda (e env)
                  (cond
                    [(int? e) e]
                    [(true? e) e]
                    [(false? e) e]
                                        
                    [(if-then-else? e) (let ([pogoj (mii (if-then-else-condition e) env)])
                                         (cond
                                           [(true? pogoj) (mii (if-then-else-e1 e) env)]
                                           [(false? pogoj) (mii (if-then-else-e2 e) env)]
                                           [#t (error "if-then-else: bad condition")]))]
                    [(is-int? e) (if (int? (mii (is-int-e1 e) env)) (true) (false))]
                    [(is-bool? e) (let ([val (mii (is-bool-e1 e) env)]) (if (or (true? val) (false? val)) (true) (false)))]
                    
                    [(add? e) (let ([val_e1 (mii (add-e1 e) env)] [val_e2 (mii (add-e2 e) env)])
                                (cond
                                  [(and (int? val_e1) (int? val_e2)) (int (+ (int-n val_e1) (int-n val_e2)))]
                                  [#t (error "add: supported only for int ->" val_e1 val_e2)]))]
                    
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
                    
                    
                    [(!? e) (let ([val_e1 (mii (!-e1 e) env)])
                              (cond
                                [(true? val_e1) (false)]
                                [(false? val_e1) (true)]
                                [#t (error "!: defined only for bool ->" val_e1)]))]

                    [#t (error "mi: invalid expression ->" e)]
                    ))])

    (mii izraz null)))

; TESTS
;(equal? (mi (int 5)) (int 5))
;(equal? (mi (false)) (false))
;(equal? (mi (add (int 1) (int 2))) (int 3))
;(equal? (mi (gt (int 2) (int 2))) (false))
;(equal? (mi (both (gt (int 2) (int 1)) (true))) (true))
;(equal? (mi (! (false))) (true))
;(equal? (mi (is-int (int 5))) (true))
;(equal? (mi (if-then-else (true) (int 5) (add (int 2) (int "a")))) (int 5))
;(equal? (ifte (true) then (add (int 1) (int 1)) else (int 3)) (if-then-else (true) (add (int 1) (int 1)) (int 3)))
;(equal? (lt (add (int 1) (int 1)) (int 4)) (gt (int 4) (add (int 1) (int 1))))