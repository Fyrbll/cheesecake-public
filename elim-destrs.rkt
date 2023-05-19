#lang racket/base

(require
 (only-in racket/function conjoin curry curryr disjoin)
 (only-in racket/list first filter-not)
 (only-in racket/match match match-define match-let match-let*)
 cheesecake/expr
 cheesecake/structs
 cheesecake/macros
 cheesecake/list
 "./counter.rkt"
 "env.rkt"
 fancy-app)
(provide
 (all-defined-out))


(define (expr-destr expr)
  (match expr
    ((? (disjoin integer? symbol?))
     #f)
    ((ITE test-expr then-expr else-expr)
     (ormap expr-destr (list test-expr then-expr else-expr)))
    ((Call* (or 'unbool 'unint 'car 'cdr) (? expr-var?))
     expr)
    ((Call function exprs)
     (ormap expr-destr exprs))))


(define (expr--elim-destrs)
  (define goals-hist
    (Env--goals-hist env))
  (match-define (Tuple cursor goals)
    (first goals-hist))
  (match-define (Tuple prefix (:: goal suffix))
    (split-at goals cursor))
  (match-define (Tuple success? subgoals)
    (expr--elim-destrs--helper goal))
  (define new-goals
    (append prefix subgoals suffix))
  (when success?
    (set-Env-goals-hist! env (cons (Tuple cursor new-goals) goals-hist)))
  success?)


(define (expr--elim-destrs--helper goal)
  (let* ((formals (Goal-formals goal))
         (doms (Goal-doms goal))
         (prems (Goal-prems goal))
         (fa-prems (Goal--fa-prems goal))
         (concl (Goal-concl goal))
         (schemes (Goal-schemes goal))
         (?destr-expr (ormap expr-destr (:: concl prems))))
    (if ?destr-expr
        (match-let*
            (((list expr names sorts guard constr)
              (match ?destr-expr
                ((Call* 'unbool expr)
                 (let ((name (fresh! '_b)))
                   (list
                    expr
                    (list name)
                    (list 'Bool)
                    (Call* 'is-bool expr)
                    (Call* 'bool name))))
                ((Call* 'unint expr)
                 (let ((name (fresh! '_z)))
                   (list
                    expr
                    (list name)
                    (list 'Int)
                    (Call* 'is-int expr)
                    (Call* 'int name))))
                ((Call* (or 'car 'cdr) expr)
                 (let ((name0 (fresh! '_v))
                       (name1 (fresh! '_v)))
                   (list
                    expr
                    (list name0 name1)
                    (list 'Value 'Value)
                    (Call* 'is-cons expr)
                    (Call* 'cons name0 name1))))))

             (replace-pe (lambda (body)
                           (expr-pe
                            (expr-replace body constr expr))))

             (goal0 (struct-copy Goal goal
                                 (prems (:: (Call* 'not guard) (map expr-pe prems)))))

             (goal1 (struct-copy Goal goal
                                 (formals (append names formals))
                                 (doms (append sorts doms))
                                 (prems (filter-not (eq? 'true _) (map replace-pe prems)))
                                 (concl (replace-pe concl))))

             ((Tuple _ goals) (expr--elim-destrs--helper goal1)))
          (Tuple #t (:: goal0 goals)))
        (Tuple #f (list goal)))))


(define (expr-replace expr to from)
  (match expr
    ((? integer?)
     expr)
    ((? (conjoin symbol? (curry equal? from)))
     to)
    ((? symbol?)
     expr)
    ((ITE test-expr then-expr else-expr)
     (ITE (expr-replace test-expr to from)
          (expr-replace then-expr to from)
          (expr-replace else-expr to from)))
    ((and (Call function exprs) (? (curry equal? from)))
     to)
    ((Call function exprs)
     (Call function (map (curryr expr-replace to from) exprs)))))


(define (expr-pe expr)
  (match expr
    ((or (? integer?)
         (? symbol?))
     expr)
    ((ITE test-expr then-expr else-expr)
     (ITE (expr-pe test-expr) (expr-pe then-expr) (expr-pe else-expr)))
    ((Call* 'not bexpr)
     (match (expr-pe bexpr)
       ['true 'false]
       ['false 'true]
       [s (Call* 'not s)]))
    ((Call* 'is-cons cons-expr)
     (match (expr-pe cons-expr)
       ((Call* 'cons _ _)
        'true)
       ((Call* (? (curryr member (list 'nil 'bool 'int))) _ _)
        'false)
       (cons-expr^
        (Call* 'is-cons cons-expr^))))
    ((Call* 'is-nil cons-expr)
     (match (expr-pe cons-expr)
       ((Call* 'cons _ _)
        'false)
       ((Call* (? (curryr member (list 'nil))) _ _)
        'true)
       (cons-expr^
        (Call* 'is-nil cons-expr^))))
    ((Call* 'car cons-expr)
     (match (expr-pe cons-expr)
       ((Call* 'cons car-expr _) car-expr)
       (cons-expr^               (Call* 'car cons-expr^))))
    ((Call* 'cdr cons-expr)
     (match (expr-pe cons-expr)
       ((Call* 'cons _ cdr-expr) cdr-expr)
       (cons-expr^               (Call* 'cdr cons-expr^))))
    ((Call* 'is-int int-expr)
     (match (expr-pe int-expr)
       ((Call* 'int _)
        'true)
       ((Call* (? (curryr member (list 'nil 'bool 'cons))) _)
        'false)
       (int-expr^
        (Call* 'is-int int-expr^))))
    ((Call* 'unint int-expr)
     (match (expr-pe int-expr)
       ((Call* 'int z) z)
       (int-expr^      (Call* 'unint int-expr^))))
    ((Call* 'is-bool bool-expr)
     (match (expr-pe bool-expr)
       ((Call* 'bool _)
        'true)
       ((Call* (? (curryr member (list 'nil 'int 'cons))) _)
        'false)
       (int-expr^
        (Call* 'is-bool int-expr^))))
    ((Call* 'unbool bool-expr)
     (match (expr-pe bool-expr)
       ((Call* 'bool b) b)
       (bool-expr^      (Call* 'unbool bool-expr^))))
    ((Call function exprs)
     (Call function (map expr-pe exprs)))))


#| Procedure
;; ---------
;; 1. Apply `expr-destr` to your goal `expr`.
;; 2. If it returns `#f`, we're done.
;; 3. If it returns anything else, a truthy value, it must be a destructor.
;; 4. Based on the destructor, pick an elimination lemma.
;; 5. Substitute the argument to the destructor for the `formal` in the 
;; elimination lemma to receive a substituted premise as well as a substituted
;; identity. 
;; 6. Produce two goals, one where the substituted premise is true and another
;; where the substituted premise is false (the negation of the substituted 
;; premise).
;; 7. Create `length(fields)` number of fresh variables and pair up each with a
;; substituted field.
;; 8. 'Generalize' the substituted fields with their variables. Also substitute
;; the more complex expression for the substituted formal everywhere you can.
|#

#| Examples
;; --------
;; Suppose I have `unbool(car(v))`, I would introduce the variable `b` and then
;; replace all occurrences of `car(v)` with `bool(b)` and eventually receive
;; one goal that starts with the premise `not(is-bool(car(v)))` and another goal
;; with no new initial premise, just `car(v)` replaced with `bool(b)` in all
;; situations. The second goal can be partially evaluated.
|#
