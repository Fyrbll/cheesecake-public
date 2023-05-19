#lang racket/base

(require
 cheesecake/list
 cheesecake/macros
 cheesecake/structs
 (only-in racket/function thunk)
 (only-in racket/list first list-set rest)
 (only-in racket/match match match-let match-let* match-lambda match-lambda** match-define)
 (only-in racket/syntax format-symbol)
 racket/dict
 "./env.rkt"
 fancy-app)
(provide repl-prove send-to-solver check-sat bracket-solver display-fork log-cheesecake-sat-debug
         assert-sat)

(define (get-from-solver out)
  (define from-solver (read out))
  (log-cheesecake-sat-debug "read from z3: ~s" from-solver)
  from-solver)

(define (display-fork form out)
  (log-cheesecake-sat-debug "sending ~s to z3" form)
  (with-output-to-file "debug.txt"
    (thunk (write form) (newline))
    #:exists 'append)
  (write form out))



(define (send-to-solver #:proc [proc (Env-proc env)] #:result [-get-from-solver get-from-solver] . ms)
  (define get-from-solver (or -get-from-solver void))
  (define in (Process-in proc))
  (define out (Process-out proc))
  (for ([m ms]) (display-fork m in))
  (newline in)
  (flush-output in)
  (define r (get-from-solver out))
  r)

(define (bracket-solver #:proc [proc (Env-proc env)] f)
  (define (emit v) (display-fork v (Process-in proc)))
  (emit '(push))
  (dynamic-wind
    void
    (thunk (f emit))
    (thunk (emit '(pop)))))

; like check-sat but for a single assert
(define (assert-sat e #:proc [proc (Env-proc env)])
  (check-sat proc (lambda (emit) (emit `(assert ,e))) #:core? #f))


(define (check-sat proc f #:core? [core? #f])
  (bracket-solver
   (lambda (emit)
     (f emit)
     (define from-solver
       (send-to-solver #:proc proc
                       `(check-sat-using (try-for default ,(timeout)))))
     (match from-solver
       ('unsat
        (define core (if core?
                         (send-to-solver #:proc proc '(get-unsat-core))
                         #f))
        (unsat core))
       ('sat (sat))
       ('unknown (unknown))))))


(define (repl-prove)
  (match-let* ((recfuns (Env-recfuns env))
               (goals-hist (Env--goals-hist env))
               (proc (Env-proc env))
               ((Tuple cursor goals) (first goals-hist))
               ((Goal goal-formals goal-doms goal--fa-prems goal-prems goal-concl _)
                 (list-ref goals cursor))
               (named-prems--add
                (match-lambda**
                 ((prem (and acc (Tuple named-prems ct)))
                  (Tuple
                   (:: (Tuple (format-symbol "prem~a" ct) prem) named-prems)
                   (+ 1 ct)))))
               ((Tuple named-prems _) (foldl named-prems--add
                                             (Tuple null 0)
                                             goal-prems)))
    (define solver-result
      (check-sat
       #:core? #t
        proc
        (lambda (emit)
          (for ((recfun recfuns))
            (match-define (RecFun id formals _ doms _ body _ _ pats _ _) recfun)
            (emit
             `(assert
               (forall ,(map doubleton formals doms)
                       (! (= ,(Call id formals) ,body)
                          :pattern ,pats)))))
          (emit
           `(assert
             (forall ((v Value))
                     (! (= (size v)
                           (ite (is-cons v)
                                (+ 1 (size (car v)) (size (cdr v)))
                                0))
                        :pattern ((size v))))))
          (for ((formal goal-formals) (dom goal-doms))
            (emit `(declare-const ,formal ,dom)))
          (for ((named-prem named-prems))
            (match-let (((Tuple name prem) named-prem))
              (emit `(assert (! ,prem :named ,name)))))
          (for ((fa-prem goal--fa-prems))
            (emit `(assert ,fa-prem)))
          (emit `(assert (not ,goal-concl))))))
    (match solver-result
      ((unsat core)
       (set-box! last--unsat-core
                 (map (dict-ref named-prems _) core))
       (update-Env--goals-hist! env
                                (match-lambda
                                  ((:: (Tuple cursor goals) rest--goals-hist)
                                   (let* ((goals^ (list-remove goals cursor))
                                          (goals^^ (if (null? goals^)
                                                       (list
                                                        (Goal null null null null 'true null))
                                                       goals^))
                                          (cursor^ (if (equal? cursor (length goals^^))
                                                       (- cursor 1)
                                                       cursor)))
                                     (:: (Tuple cursor^ goals^^)
                                         (:: (Tuple cursor goals)
                                             rest--goals-hist))))))
       #t)
      ((sat)
       (set-Env--goals-hist! env
                             (list (Tuple 0 (Goal null null null null 'false null))))
       #f)
      (_
       #f))))

(define-logger cheesecake-sat)
