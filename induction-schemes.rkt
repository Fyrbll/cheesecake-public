#lang racket/base

(require
 (only-in racket/pretty pretty-print-columns
          pretty-print-current-style-table
          pretty-print-extend-style-table pretty-print)
 (only-in racket/match match match-let match-let* match-lambda define/match
          match-define)
 (only-in racket/dict dict-ref)
 (only-in racket/list append-map remove-duplicates make-list list-set first
          second third drop range rest filter-not)
 (only-in racket/function identity curry curryr conjoin disjoin negate thunk)
 (only-in racket/set set set-add set-member? set->list set-empty? set-intersect
          list->set)
 cheesecake/expr
 cheesecake/list
 cheesecake/structs
 cheesecake/macros
 "repl-prove.rkt"
 "./env.rkt"
 (only-in "./load.rkt" make-and))
(provide
 (all-defined-out))

(define Formals list)
(define Actuals list)

(define whileloop-RecFun
  (let ((id 'whileloop)
        (formals (list 'i 'max 'x))
        (measureds (list #t #t #f))
        (doms (list 'Int 'Int 'Int))
        (rng 'Int)
        (tips (list (Tip (list '(< i max) '(not (pred i x)))
                         (list (list '(+ i 1) 'max '(fn x)))))))
    (RecFun id formals measureds doms rng #f tips #f #f #f #f)))

;; Changeables. [k]
;; Unchangeables. [x, y]
(define call_1
  '(whileloop k (+ x y) v))

;; Changeables. [k]
;; Unchangeables. [x]
(define call_2
  '(whileloop k (g x) x))

;; Changeables. [i]
;; Unchangeables. [max]
(define call_3
  '(whileloop i max i))

(define call_4
  '(whileloop k (+ x y) k))

(define call_5
  '(whileloop x y (h z)))

;; Changeables. [g(i)]
;; Unchangeables. [max]
(define call_6
  '(whileloop (g i) max x))

;; Changeables. [i]
;; Unchangeables. [i]
(define call_7
  '(whileloop i (g i) x))


(define Row list)
(define Row-measd first)
(define Row-formal second)
(define Row--formal-actuals rest)


(define (Call-table call)
  (let* ((call-function (first call))
         (call-actuals (rest call))
         (?recfun (findf (compose (curry equal? call-function) RecFun-id)
                         (Env-recfuns env))))
    (and ?recfun
         (let* ((measds (RecFun-measureds ?recfun))
                (formals (RecFun-formals ?recfun))
                (actuals* (append-map Tip-actuals* (RecFun-tips ?recfun)))
                (table (apply (curry map Row)
                              (:: measds (:: formals actuals*))))
                (substn (map Tuple formals call-actuals)))
           (map (lambda (row)
                  (map (lambda (x)
                         (if (boolean? x) x (expr-subst x substn)))
                       row))
                table)))))


(define (Call-changeables call (table #f))
  (let ((table (or table (Call-table call))))
    (and table
         (remove-duplicates
          (map Row-formal
               (filter (compose >1-distinct? Row--formal-actuals)
                       (filter Row-measd table)))))))


(define (Call-unchangeables call (table #f))
  (let ((table (or table (Call-table call))))
    (and table
         (set->list
          (exprs--var-set
           (map Row-formal
                (filter (compose 1-distinct? Row--formal-actuals)
                        (filter Row-measd table)))
           (set))))))


(define (Call-unchanging call (?table #f))
  (let ((?table (or ?table (Call-table call))))
    (and ?table
         (exprs--var-set
          (for/list ((row ?table)
                     #:when (1-distinct? (Row--formal-actuals row)))
            (Row-formal row))
          (set)))))


(define (Call-applicable? call (?table #f))
  (let* ((?table (or ?table (Call-table call)))
         (?changeables (Call-changeables call ?table))
         (?unchangeables (Call-unchangeables call ?table)))
    (and (pair? ?changeables)
         (null? (filter-not expr-var? ?changeables))
         ?unchangeables
         (set-empty?
          (set-intersect
           (list->set ?changeables)
           (list->set ?unchangeables))))))


(define (Env-recfuns--ref env id)
  (findf (compose (curry equal? id) RecFun-id) (Env-recfuns env)))


(define (Call-scheme call)
  (let* ((call-function (first call))
         (call-actuals (rest call))
         (?recfun (Env-recfuns--ref env call-function)))
    (and ?recfun
         (let* ((unchangeables (Call-unchangeables call))
                (measds (RecFun-measureds ?recfun))
                (formals (RecFun-formals ?recfun))
                (doms (RecFun-doms ?recfun))
                (indn (RecFun-indn ?recfun))
                (tips (RecFun-tips ?recfun))
                (substn (map Tuple formals call-actuals))
                (exprs-subst (curry map (curryr expr-subst substn)))
                (mask (mask--rem-dups
                       (for/list ((substed-formal (exprs-subst formals)))
                         (and (expr-var? substed-formal)
                              (not (member substed-formal unchangeables))
                              substed-formal))
                       measds))
                (ihs (make-ihs indn mask exprs-subst))
                (proc (Env-proc env))
                (in (Process-in proc)))
           (match-define (Tuple cursor goals) (first (Env--goals-hist env)))
           (define goal (list-ref goals cursor))
           (bracket-solver
            (lambda (emit)
             (for ((var (Goal-formals goal))
                   (dom (Goal-doms goal)))
               (emit `(declare-const ,var ,dom)))
             (make-cases tips ihs formals doms exprs-subst)))))))


(define (make-cases tips ihs formals doms exprs-subst (base null) (acc null))
  (match tips
    ((list)
     (reverse (:: (Tip base null) acc)))
    ((:: tip rest-tips)
     (let* ((tests (exprs-subst (Tip-tests tip)))
            (substns (tests-substns tests ihs formals doms)))
       (make-cases rest-tips ihs formals doms exprs-subst
                   (:: (exprs-or (map expr-negate tests)) base)
                   (:: (Tip tests substns) acc))))))


(define (tests-substns tests ihs formals doms (acc null))
  (match ihs
    ((list)
     (reverse acc))
    ((:: tip rest-tips)
     (let* ((reqs (Tip-tests tip))
            (substns (Tip-actuals* tip))
            (goal (Call* '=> (Call 'and tests) (Call 'and reqs)))
            (proc (Env-proc env)))
       (define r (check-sat proc (lambda (emit) (emit `(assert (not ,goal))))))
       (match r
         ((unsat _)
          (tests-substns tests rest-tips formals doms (append substns acc)))
         (_
          (tests-substns tests rest-tips formals doms acc)))))))


(define (mask--rem-dups mask measds)
  (vector->list
   (mask--rem-dups--helper (list->vector mask)
                           (list->vector measds)
                           0)))


(define (mask--rem-dups--helper mask measds idx)
  (if (< idx (vector-length mask))
      (let ((?var (vector-ref mask idx)))
        (if ?var
            (let* ((var-idxs (vector--indexes-of mask ?var))
                   (var-measd-idxs (filter (curry vector-ref measds) var-idxs))
                   (keep-idx (first (append var-measd-idxs var-idxs)))
                   (throw-idxs (remove keep-idx var-idxs)))
              (for ((throw-idx throw-idxs))
                (vector-set! mask throw-idx #f))
              (mask--rem-dups--helper mask measds (+ idx 1)))
            (mask--rem-dups--helper mask measds (+ idx 1))))
      mask))


(define (vector--indexes-of v e (i (- (vector-length v) 1)) (acc null))
  (if (< i 0)
      acc
      (if (equal? (vector-ref v i) e)
          (vector--indexes-of v e (- i 1) (:: i acc))
          (vector--indexes-of v e (- i 1) acc))))


(define (make-ihs tips mask exprs-subst (acc null))
  (match tips
    ((list)
     (reverse acc))
    ((:: tip rest-tips)
     (let* ((tests (Tip-tests tip))
            (substed-tests (exprs-subst tests))
            (actuals* (Tip-actuals* tip))
            (substns (for/list ((actuals actuals*))
                       (for/list ((?var mask)
                                  (actual (exprs-subst actuals))
                                  #:when ?var
                                  #:unless (equal? ?var actual))
                         (Tuple ?var actual))))
            (substed-tip (Tip substed-tests substns)))
       (make-ihs rest-tips mask exprs-subst (:: substed-tip acc))))))


(define (induct call)
  (match-let*
      ((goals-hist (Env--goals-hist env))
       ((Tuple cursor goals) (first goals-hist))
       ((Tuple goals-prefix (:: goal goals-suffix)) (split-at goals cursor))
       (formals (Goal-formals goal))
       (doms (Goal-doms goal))
       (fa-prems (Goal--fa-prems goal))
       (prems (Goal-prems goal))
       (concl (Goal-concl goal))
       (schemes (Goal-schemes goal))
       (demoted (Call '=> (append prems (list concl))))
       (subgoals (for/list ((case_ (Call-scheme call)))
                   (let* ((case-prems (Tip-tests case_))
                          (substns (Tip-actuals* case_))
                          (indn-hyps (for/list ((substn substns))
                                       (expr-subst demoted substn)))
                          (new-prems (append prems case-prems indn-hyps))
                          (new-schemes (:: (first call) schemes)))
                     (struct-copy Goal goal
                                  (prems new-prems)
                                  (schemes new-schemes)))))
       (new-goals (append goals-prefix subgoals goals-suffix)))
    (update-Env--goals-hist! env (curry :: (Tuple cursor new-goals)))))


#|;;;;;;;;
;; STASH ;
;;;;;;;;|#
#|
(define ackermann-peter-machine
  (Machine 'ackermann-peter (Formals (cons 'm #t) (cons 'n #t))
    (list
     (Tip (list '(>= m 0) '(>= n 0) '(not (= m 0)) '(= n 0))
          (list (Actuals '(- m 1) 1)))
     (Tip (list '(>= m 0) '(>= n 0) '(not (= m 0)) '(not (= n 0)))
          (list (Actuals '(- m 1) '(A m (- n 1)))
                (Actuals 'm '(- n 1)))))))

(define monus-machine
  (Machine 'monus (Formals (cons 'n #t) (cons 'm #f))
    (list
     (Tip (list '(is-cons n) '(is-cons m))
          (list (Actuals '(cdr n) '(cdr m)))))))

(define is-natural-machine
  (Machine 'is-natural (Formals (cons 'v #t))
    (list
     (Tip (list '(is-cons v)) (list (Actuals '(cdr v)))))))

(define gt-machine
  (Machine 'gt (Formals (cons 'n #t) (cons 'm #f))
    (list
     (Tip (list '(is-cons n) '(is-cons m))
          (list (Actuals '(cdr n) '(cdr m)))))))

(define minimum-machine
  (Machine 'minimum (Formals (cons 'm #f) (cons 'n #t))
    (list
     (Tip (list '(is-cons n))
          (list (Actuals '(cdr m) '(cdr n)))))))


(define call_8
  '(ackermann-peter x x))

(define call_9
  '(ackermann-peter x y))

(define call_10
  '(monus n (cons nil m)))

(define call_11
  '(monus n m))

(define call_12
  '(is-natural n))

(define call_13
  '(gt n m))

(define call_14
  '(minimum x y))
|#
