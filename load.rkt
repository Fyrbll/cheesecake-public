#lang racket/base

(require
 (only-in racket/function disjoin thunk)
 (only-in racket/list append-map first remove-duplicates second rest)
 (only-in racket/match match match* match-let match-let* match-define)
 (only-in racket/port port->list with-input-from-string with-output-to-string)
 (only-in racket/set proper-subset? set set-add set-empty? set-map set-member?)
 racket/file
 (only-in racket/string string-join)
 (only-in racket/syntax format-symbol)
 (only-in racket/system process)
 cheesecake/structs
 cheesecake/expr
 cheesecake/macros
 cheesecake/list
 "./env.rkt"
 "./repl-prove.rkt"
 "./undo.rkt"
 fancy-app)
(provide
 (all-defined-out))


(define std-prefix
  `((declare-datatype
     Value
     ((nil) (bool (unbool_ Bool)) (int (unint_ Int)) (cons (car_ Value) (cdr_ Value))))
    (define-fun unbool ((v Value)) Bool (ite (is-bool v) (unbool_ v) false))
    (define-fun unint ((v Value)) Int (ite (is-int v) (unint_ v) 0))
    (define-fun car ((v Value)) Value (ite (is-cons v) (car_ v) nil))
    (define-fun cdr ((v Value)) Value (ite (is-cons v) (cdr_ v) nil))
    (define-fun nat< ((m Int) (n Int)) Bool (and (or (> m 0) (> n 0)) (< m n)))))

(define size-fun
  (list '(declare-fun size (Value) Int)
        '(assert (forall ((v Value))
                         (! (ite (is-cons v)
                                 (and (>= (size (car_ v)) 0)
                                      (>= (size (cdr_ v)) 0)
                                      (= (size v) (+ 1 (size (car_ v)) (size (cdr_ v)))))
                                 (= (size v) 0))
                            :pattern
                            ((size v)))))))

(define config-options
  (list '(set-option :auto_config false)
        '(set-option :smt.mbqi false)
        '(set-option :smt.ematching true)
        '(set-option :unsat_core true)
        '(set-option :smt.core.minimize true)))

(define (repl-load file)
  (match-define (list out in id err sig-snd) (process "z3 -in" #:set-pwd? #t))
  (define P (Process id in out err sig-snd))
  (apply send-to-solver #:proc P #:result #f std-prefix)
  (set-Env-proc! env P)

  (for ([form (file->list file)])
    (form-load form))
  (apply send-to-solver #:proc P #:result #f config-options)
  (apply send-to-solver #:proc P #:result #f size-fun)

  (update-Env-recfuns! env (map recfun-revise _)))


(define (form-load form)
  (match form
    (`(define-fun ,id ,(list (list formals doms) ...) ,rng
        ,body)
     (send-to-solver form #:proc (Env-proc env) #:result #f)
     (update-Env-funs! env
       (cons (Fun id formals doms rng body) _)))

    (`(define-fun-rec ,id ,(list (list formals doms) ...) ,rng
        ,body
        (:measure ,meas)
        (:relation ,reln))
     (let* ((pat (Call id formals))
            [proc (Env-proc env)])
       (send-to-solver #:proc proc #:result #f  `(declare-fun ,id ,doms ,rng))
       (bracket-solver
        #:proc proc
        (lambda (emit)
          (for ((formal formals)
                (dom doms))
            (emit `(declare-const ,formal ,dom)))
          (let* ((measds (map (expr-has-var? meas _) formals))
                 (nbody ((compose
                          expr-normalize
                          expr-desugar
                          (expr-inline _ (Env-funs env)))
                         body))
                 (tips (expr-tips nbody id)))
            (Env-recfuns-cons! env
                               (RecFun id formals measds doms rng body tips #f
                                       (list pat) meas reln)))))))

    (`(prove (forall ,(list (list formals doms) ...) ,body))
     (match body
       (`(=> ,@prems ,concl)
        (define hist (Env-goals-hist env))
        (match-define (Tuple cursor goals) (if (null? hist)
                                               (Tuple 0 null)
                                               (first hist)))
        (set-Env--goals-hist! env
                              (list (Tuple 0 (cons (Goal formals doms null prems concl null) goals)))))))))


(define (expr-tips expr id)
  (stack-tips (list (Tuple expr null)) id null))


(define (stack-tips stack id acc)
  (let* ((proc (Env-proc env))
         (in (Process-in proc))
         (out (Process-out proc))
         (err (Process-err proc))
         (sig-snd (Process-sig-snd proc)))
    (match stack
      ((list)
       acc)

      ((:: (Tuple expr tests) rest-stack)
       (match expr
         ((? (disjoin integer? symbol?))
          (stack-tips rest-stack id acc))

         ((Call _ _)
          #:when (set-empty? (expr-calls expr (list id)))
          (stack-tips rest-stack id acc))

         ((Call _ _)
          (let* ((actuals* (set-map (expr-calls expr (list id)) rest))
                 (tip (Tip (reverse tests) actuals*)))
            (stack-tips rest-stack id (:: tip acc))))

         ((ITE test-expr then-expr else-expr)
          #:when (set-empty? (expr-calls test-expr (list id)))
          (match-let*
              ((not--test-expr (Call* 'not test-expr))
               (then-tests (:: test-expr tests))
               (then-tuple (Tuple then-expr then-tests))
               (else-tests (:: not--test-expr tests))
               (else-tuple (Tuple else-expr else-tests)))
            (define new-l
              (bracket-solver
               #:proc proc
               (lambda (emit)
                 (for ((test tests))
                   (emit `(assert ,test)))
                 (cond [(unsat? (assert-sat test-expr))
                        (:: else-tuple rest-stack)]
                       [(unsat? (assert-sat not--test-expr))
                        (:: then-tuple rest-stack)]
                       [else
                        (:: then-tuple (:: else-tuple rest-stack))]))))
            (stack-tips new-l id acc)))


         ((ITE _ _ _)
          (let* ((actuals* (set-map (expr-calls expr (list id)) rest))
                 (tip (Tip (reverse tests) actuals*)))
            (stack-tips rest-stack id (:: tip acc)))))))))

(define (recfun-revise recfun)
  (let* ((formals (RecFun-formals recfun))
         (doms (RecFun-doms recfun))
         (tips (RecFun-tips recfun))
         (meas (RecFun-meas recfun))
         (reln (RecFun-reln recfun))
         (indn (map (tip-revise _ formals doms meas reln) tips)))
    (struct-copy RecFun recfun (indn indn))))


(define (tip-revise tip formals doms meas reln)
  (let* ((tests (Tip-tests tip))
         (actuals* (Tip-actuals* tip))
         (concl (make-and
                 (map (actuals-concl _ formals meas reln) actuals*)))
         (goal (Goal formals doms null tests concl null)))
    (update-Env--goals-hist! env (cons (Tuple 0 (list goal)) _))
    (repl-prove)
    (repl-undo)
    (repl-undo)
    (Tip (remove-duplicates (unbox last--unsat-core)) actuals*)))


(define (actuals-concl actuals formals meas reln)
  (let ((actuals-meas (expr-subst meas (map Tuple formals actuals))))
    (expr-subst reln (list (Tuple 'x actuals-meas) (Tuple 'y meas)))))


(define (make-and clauses)
  (match clauses
    ((list)
     'true)
    ((list clause)
     clause)
    (_
     (Call 'and clauses))))
