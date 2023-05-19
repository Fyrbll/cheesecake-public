#lang racket/base

(require
 (for-syntax (only-in racket/base lambda syntax syntax-case))
 (only-in racket/function curry curryr)
 (only-in racket/list append-map drop-right first index-where list-update range
          rest remove-duplicates)
 (only-in racket/match match match-define match-let match-let*)
 (only-in racket/set for/set list->set set set->list set-add set-count subset?)
 cheesecake/expr
 cheesecake/macros
 cheesecake/structs
 "env.rkt"
 "induction-schemes.rkt")
(provide
 (all-defined-out))


(define (suggest)
  (match-define (Tuple cursor goals)
    (first (Env--goals-hist env)))
  (define spent
    (Goal-schemes (list-ref goals cursor)))
  (define (avail? scheme)
    (not (member (first (first (Scheme-calls scheme))) spent)))
  (define schemes
    (filter
     avail?
     (sort
      (subsumption
       (collect-Schemes))
      Scheme--greater-than?)))
  schemes)


#| Creates an induction scheme, a 'Scheme' struct, for each call to a recursive
;; function in the current goal.
|#
(define (collect-Schemes)
  (match-let (((Tuple curs goals) (first (Env--goals-hist env))))
    (let ((goal (list-ref goals curs)))
      (for/list ((call (exprs-calls
                        (:: (Goal-concl goal) (Goal-prems goal))
                        (map RecFun-id (Env-recfuns env))))
                 #:when (Call-applicable? call))
        (Call-Scheme call)))))


#| Takes a call to some recursive function as input and returns its
;; corresponding 'Scheme' struct.
|#
(define (Call-Scheme call)
  (define calls
    (list call))
  (define cases
    (drop-right (Call-scheme call) 1))
  (define tests*
    (for/list ((_case cases))
      (remove-duplicates (Tip-tests _case))))
  (define substns
    (for/foldr ((substns null))
      ((_case cases))
      (append (Tip-substns _case) substns)))
  (define changing
    (for*/foldr ((changing (set)))
      ((substn substns)
       (tuple substn))
      (set-add changing (car tuple))))
  (define unchanging
    (Call-unchanging call))
  (define formal-ct
    (for/first ((recfun (Env-recfuns env))
                #:when (equal? (RecFun-id recfun) (first call)))
      (length (RecFun-formals recfun))))
  (define score
    (/ (set-count changing) formal-ct))
  (Scheme calls cases tests* substns changing unchanging score))


#| Returns '#t' when induction scheme S2 subsumes induction scheme S1 and
;; returns '#f' otherwise.
|#
(define (subsumes? s2 s1)
  (let* ((tests*2 (Scheme-tests* s2))
         (substns2 (Scheme-substitutions s2))
         (changing2 (Scheme-changing s2))
         (unchanging2 (Scheme-unchanging s2))
         (tests*1 (Scheme-tests* s1))
         (substns1 (Scheme-substitutions s1))
         (changing1 (Scheme-changing s1))
         (unchanging1 (Scheme-unchanging s1)))
    (and (subset? changing1 changing2)
         (subset? unchanging1 unchanging2)
         (let ((tests*-subsumed (tests*-subsumes? tests*2 tests*1)))
           ;;(printf "[debug] tests*: ~a~n" tests*-subsumed)
           tests*-subsumed)
         (let ((substns-subsumed (substns-subsumes? substns2 substns1)))
           ;;(printf "[debug] substns: ~a~n" substns-subsumed)
           substns-subsumed))))


(define (tests*-subsumes? tests*2 tests*1)
  (subsumes?-helper tests*2 tests*1 subset?))


(define (substns-subsumes? substns2 substns1)
  (subsumes?-helper substns2 substns1 subsubstn?))


#| SUBSTN1 and SUBSTN2 are substitutions represented as association lists.
;; This function returns #t when both conditions are met
;; - the domain of SUBSTN1 is a subset of the domain of SUBSTN2
;; - for every x in the domain of SUBSTN1, SUBSTN1(x) is a subterm of
;; SUBSTN2(x)
;; The function returns #f otherwise.
|#
(define (subsubstn? substn1 substn2)
  (for/fold ((result #t))
            ((pair1 substn1))
    (and result
         (let* ((var (car pair1))
                (expr1 (cdr pair1))
                (pair2 (assoc var substn2)))
           (and pair2
                (let ((expr2 (cdr pair2)))
                  (expr-subterm? expr1 expr2)))))))


#| Returns #t when EXPR1 is a subterm of EXPR2, returns #f otherwise.
|#
(define (expr-subterm? expr1 expr2)
  (match expr2
    ((? integer?)
     (equal? expr1 expr2))
    ((? symbol?)
     (equal? expr1 expr2))
    ((ITE test-expr then-expr else-expr)
     (or (equal? expr1 expr2)
         (expr-subterm? expr1 test-expr)
         (expr-subterm? expr1 then-expr)
         (expr-subterm? expr1 else-expr)))
    ((Call _ exprs)
     (or (equal? expr1 expr2)
         (ormap (curry expr-subterm? expr1) exprs)))))


#| invariant. `continue` is always non-empty.
|#
(define (subsumes?-helper ys xs reln)
  (define n (length ys))
  (define m (length xs))
  (define k* (range n))
  (define (recur partial continue)
    (let/cc return
      (define i (length partial))
      (when (= i m)
        (return (reverse partial)))
      (define x_i (list-ref xs i))
      (define lower (first continue))
      (define (backtrack)
        (if (= i 0)
            (return #f)
            (return (recur (rest partial) (rest continue)))))
      (unless lower (backtrack))
      (define j (for/first ((k k*)
                            (y_k ys)
                            #:when (and (>= k lower)
                                        (not (member k partial))
                                        (reln x_i y_k)))
                  k))
      (unless j (backtrack))
      (define j++ (and (< j (- n 1)) (+ j 1)))
      (recur (:: j partial) (:: 0 (:: j++ (rest continue))))))
  (recur null (list 0)))


#| Runs subsumption analysis on SCHEMES in the hope of eliminating schemes
;; that are less effective.
|#
(define (subsumption schemes)
  (if (null? schemes)
      null
      (subsumption-helper null (first schemes) (rest schemes))))


(define (updater lst winner-index loser)
  (list-update
   lst
   winner-index
   (lambda (winner)
     (struct-copy
      Scheme
      winner
      (calls (append (Scheme-calls winner) (Scheme-calls loser)))
      (score (+ (Scheme-score winner) (Scheme-score loser)))))))


(define (index-of-winner lst scheme1)
  (index-where lst (lambda (scheme2) (subsumes? scheme2 scheme1))))


(define (subsumption-helper prefix current suffix)
  (define prefix-winner-index
    (index-of-winner prefix current))
  (define new-prefix
    (if prefix-winner-index
        (updater prefix prefix-winner-index current)
        prefix))
  (define suffix-winner-index
    (and (not prefix-winner-index)
         (index-of-winner suffix current)))
  (define new-suffix
    (if suffix-winner-index
        (updater suffix suffix-winner-index current)
        suffix))
  (define suffix-empty
    (null? suffix))
  (define winner-exists
    (or prefix-winner-index suffix-winner-index))
  (cond
    ((and suffix-empty winner-exists)
     new-prefix)
    (suffix-empty
     (append new-prefix (list current)))
    (winner-exists
     (subsumption-helper new-prefix (first new-suffix) (rest new-suffix)))
    (else
     (subsumption-helper (append new-prefix (list current))
                         (first new-suffix)
                         (rest new-suffix)))))

#| STASH
;; ^^^^^

(define-syntax match-let*/Option
  (lambda (syntax_)
    (syntax-case syntax_ (match-let*/Option)
      ((match-let*/Option ()
         body ...)
       (syntax (begin body ...)))
      ((match-let*/Option ((pattern0 body0)
                           clauses
                           ...)
         body ...)
       (syntax
        (match body0
          (pattern0
           (match-let*/Option (clauses ...)
             body ...))
          (_ #f)))))))
|#
