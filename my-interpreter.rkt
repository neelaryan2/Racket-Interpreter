#lang racket
(require racket/struct)
(provide (all-defined-out))
(require "defs.rkt")
(require "examples.rkt")

(define stacks (make-vector 100))
(define stacksindex 0)

;made by Neel Aryan Gupta
; Roll no. 180050067

;;Global definitions. A counter that tracks the framenumber
(define framenumber 0)

;The stack and its operations. I have decided to make the stack a global.
(define stack '())
(define (push frame) (set! stack (cons frame stack)))
(define (pop) (if (null? stack) (error "Empty stack")
                  (set! stack (cdr stack))))
(define (top) (if (null? stack) (error "Empty stack")
                  (car stack)))


;createframe creates a new frame. It gets its number from
;;framenumber and as a side effect increases framenumber
(define (createframe hashtable parent) ;hastable gives the initial bindings
  (begin (set! framenumber (+ framenumber 1))
         (frame (- framenumber 1) hashtable parent)))

;This creates the global frame, which, in our case, contains
;empty bindings.
(push (createframe (make-hash '()) (emptyframe)))

;This interprets a program. It uses the following function processdef.
(define (eval-program prog)
  (match prog
    [(pgm deflist) (begin (set! framenumber 1) (set! stack (list (frame 0 (make-hash '()) (emptyframe))))
                          (processdeflist deflist (top))
                          (return-value-of-main (top)))]))

;;processdef describes how each definition is processed and added to
;;the frame fr.
(define (processdef defn fr)
  (match defn    
    [(def v/f exp) (begin (hash-set! (frame-bindings fr) v/f (eval-exp exp)) (void))]))

(define (processdeflist deflist fr)
  (match deflist
    [(cons a b) (if (null? b) (begin (processdef a fr) (void))
                    (begin (processdef a fr) (processdeflist b fr)))])) 

;; We have said that the result of the program is the value of
;; the symbol main. main must be a defined symbol in each program.
(define (return-value-of-main frame)
  (hash-ref! (frame-bindings frame) 'main "main not found"))

(define (zip l1 l2)
  (cond [(or (null? l1) (null? l2)) '()]
        [else (cons (cons (car l1) (car l2)) (zip (cdr l1) (cdr l2)))]))

;; The expression evaluator is the heart of the interpreter.
;; It will use the functions below
(define (eval-exp exp)
  (cond [(symbol? exp) (let ([k (symbol-value exp (top))])
                         (if (equal? k 'nosuchkey)
                             (error "Symbol not found") (eval-exp k)))]
        [(boolean? exp) exp]
        [(number? exp) exp]
        [(list? exp) (map eval-exp exp)]
        [(string? exp) exp]
        [(void? exp) exp]
        [else (match exp
                [(uexp op exp1) (op (eval-exp exp1))]
                [(bexp op exp1 exp2) (op (eval-exp exp1) (eval-exp exp2))]
                [(closure la fra) exp]
                [(lam varlist _) (closure exp (top))]
                [(app exp1 explist) (match (eval-exp exp1)
                                      [(closure lamb fram) (let ([k 1])
                                                                 ;(if (= (length explist) (length (lam-varlist lamb)))
                                                                 (begin (push (createframe (make-hash (zip (lam-varlist lamb) (eval-exp explist))) fram))
                                                                        (set! k (eval-exp (lam-exp lamb))) (pop) k)
                                                                 ;(error "Arity mismatch"))
                                                                 )]
                                      [else (error "Not a function")])]
;                 (if (symbol? exp1) (eval-exp (app (eval-exp exp1) explist))
;                                        (match exp1
;                                          [(app exp2 explist2) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(closure lamb fram) (let ([k 1])
;                                                                 ;(if (= (length explist) (length (lam-varlist lamb)))
;                                                                 (begin (push (createframe (make-hash (zip (lam-varlist lamb) (eval-exp explist))) fram))
;                                                                        (set! k (eval-exp (lam-exp lamb))) (pop) k)
;                                                                 ;(error "Arity mismatch"))
;                                                                 )]
;                                          [(lam varlist exp) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(beginexp explist) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(iff cond exp1 exp2) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(sett var exp1) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(lett deflist exp1) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(lets deflist exp1) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(beginexp explist) (eval-exp (app (eval-exp exp1) explist))]
;                                          [(defexp deflist exp1) (eval-exp (app (eval-exp exp1) explist))]
;                                          [else (error "Not a function")]))]
                ;...and so on, fill in these...
                [(iff cond exp1 exp2) (if (eval-exp cond) (eval-exp exp1) (eval-exp exp2))]
                [(sett var exp1) (hash-set! (frame-bindings (search var (top))) var (eval-exp exp1))]
                [(lett deflist exp1) (let ([k 1]) (begin (define fr1 (createframe (make-hash '()) (top)))
                                                         (processdeflist deflist fr1) (push fr1)
                                                         (set! k (eval-exp exp1)) (pop) k))]
                [(lets deflist exp1) (process-lets deflist exp1)]
                [(beginexp explist) (process-beginexp explist)]
                [(defexp deflist exp1) (begin (processdeflist deflist (top)) (eval-exp exp1))]
                [(debugexp) (begin
                 (vector-set! stacks stacksindex stack)
                 (set! stacksindex (+ 1 stacksindex)))]
                [else (error "Unknown command")])]))

;;An auxilliary function that processes a begin expression
(define (process-beginexp explist)
  (match explist
    [(cons a b) (if (null? b) (eval-exp a) (begin (eval-exp a) (process-beginexp b)))]))

;;An auxilliary function that processes a let expression.
;;The let definitions are in deflist, and the let body is exp.
(define (process-lets deflist exp)
  (let* ((len (length deflist))
        (framelist (frame-list len '())))
    (define (helper lst frlist c)
    (match lst
      [(cons a b) (if (null? b) (let ([k 1]) (begin (processdef a (list-ref frlist c)) (push (list-ref frlist c)) (fram+)
                                                    (set! k (eval-exp exp)) (set! stack (list-tail stack len)) k))
                      (begin (processdef a (list-ref frlist c)) (push (list-ref frlist c)) (fram+) (helper b frlist (+ c 1))))]))
  (begin (set! framenumber (- framenumber len)) (helper deflist framelist 0))))

(define (fram+)
  (set! framenumber (+ framenumber 1)))

(define (frame-list n acc)
  (cond [(= n 0) (reverse acc)]
        [else  (frame-list (- n 1) (cons (createframe (make-hash '()) (if (null? acc) (top) (car acc))) acc))]))

;;Prints the current environment running through a chain of frames.
;;Note that my struct definitions are such that if fr is a frame,
;;then (displayln fr) will print the frame in the format that I have
;;shown. 
(define (print-current-environment fr)
  (if (emptyframe? fr) (begin (displayln "@@@@@@@@@@@@@@@@@@@@@@@") (void))
      (begin (displayln "@@@@@@@@@@@@@@@@@@@@@@@") (displayln fr) (print-current-environment (frame-parent fr)))))

;;Search for the symbol sym in an environment that starts with the frame
;;fr. We shall make search return either the  emptyframe
;;or the frame containing the symbol (note, not the value of the
;;symbol itself.

(define (search sym fr)
  (if (emptyframe? fr) fr
      (let* ([binding (frame-bindings fr)]
             [parent (frame-parent fr)])
        (if (hash-has-key? binding sym) fr (search sym parent)))))

(define (symbol-value symb fram)
  (let ([p (search symb fram)])
    (if (emptyframe? p) (error "Symbol not found")
        (hash-ref (frame-bindings p) symb (lambda () 'nosuchkey)))))
    
(define (cleanup)
  (set!  stacks (make-vector 100))
  (set! stacksindex 0)
  (set! framenumber 0)
  (set! stack '())
  (push (createframe (make-hash '()) (emptyframe))))

