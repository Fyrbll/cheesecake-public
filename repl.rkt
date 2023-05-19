#lang racket/base

(require
 (only-in racket/set set->list list->set set set-add set-union set-empty?
          set-map for/set)
 (only-in racket/pretty pretty-print-current-style-table
          pretty-print-extend-style-table pretty-print pretty-display)
 (only-in racket/syntax format-symbol)
 (only-in racket/system system)
 (only-in racket/function conjoin curry curryr identity thunk)
 (only-in racket/list append-map take first list-set list-update partition
          second third cartesian-product range make-list add-between last
          remove-duplicates rest)
 (only-in racket/match match match-let* match-lambda match-lambda** match-let
          match* define/match match-let*-values define-match-expander
          match-define)
 (only-in racket/port port->list)
 (only-in racket/string string-join)
 ;;(only-in "./define-fun-rec-to-assert.rkt" define-fun-rec->assert)
 ;;(only-in "./eliminate-destructors.rkt" eliminate-destructors (desugar desugar-2) lift-ites evaluate identify next)
 ;;(only-in "./simplify.rkt" eliminate-define-fun eliminate-define-funs-rec)
 #;(rename-in "./sugar.rkt" (desugar_expression expression-desugar)
            (normalize_expression expression-normalize))
 ;;(only-in "./unfold.rkt" unfold depth_definition)
 (only-in "./format.rkt" rest-format)
 #;(only-in "./cnf.rkt" fake-cnf)
 ;;(only-in "../utility.rkt" substitute-_*-with-_*-in-_ calls-to-_-in-_)
 (only-in "./prove.rkt" prove)
 (only-in "./induction-schemes.rkt" Call-changeables Call-unchangeables
          Call-applicable? Call-scheme induct)
 cheesecake/structs
 cheesecake/macros
 (only-in cheesecake/list split-at)
 (rename-in cheesecake/structs (Tip indscm-Tip) (Goal cheesecake-Goal))
 "automatic.rkt"
 "./elim-destrs.rkt"
 "./env.rkt"
 "./exit.rkt"
 "./load.rkt"
 "./print-goal.rkt"
 "./print--goals-hist.rkt"
 "./print-tips.rkt"
 "./print--unsat-core.rkt"
 "./repl-prove.rkt"
 "./undo.rkt"
 "./suggest.rkt"
 (for-syntax (only-in racket/base lambda syntax syntax-case)))
(provide (all-defined-out))

(define (define-fun-rec->assert . rest)
  (void))

(define (substitute-_*-with-_*-in-_ x y z)
  (void)) 

(define (calls-to-_-in-_ x y)
  (void))

(define (eliminate-destructors . rest)
  (void))

(define (desugar-2 . rest)
  (void))

(define (lift-ites . rest)
  (void))

(define (evaluate . rest)
  (void))

(define (identify . rest)
  (void))

(define (next . rest)
  (void))

(define (eliminate-define-fun . rest)
  (void))

(define (eliminate-define-funs-rec . rest)
  (void))

(define (expression-desugar . rest)
  (void))

(define (expression-normalize . rest)
  (void))

(define (unfold . rest)
  (void))

(define (depth_definition . rest)
  (void))

(define (fake-cnf . rest)
  (void))

(define (normalize . rest)
  (void))

(define-for-syntax cons-expander
  (lambda (input-syntax)
    (syntax-case input-syntax ()
      ((_ car-syntax cdr-syntax)
       (syntax (cons car-syntax cdr-syntax))))))

(define-match-expander :: cons-expander cons-expander)

(define-match-expander tuple cons-expander cons-expander)

(define-match-expander ite
  (lambda (input-syntax)
    (syntax-case input-syntax ()
      ((_ test-syntax then-syntax else-syntax)
       (syntax (list 'ite test-syntax then-syntax else-syntax)))))
  (lambda (input-syntax)
    (syntax-case input-syntax ()
      ((_ test-syntax then-syntax else-syntax)
       (syntax (ite-helper test-syntax then-syntax else-syntax))))))

(define-match-expander invoke
  (lambda (input-syntax)
    (syntax-case input-syntax ()
      ((_ function arguments)
       (syntax (cons (and function
                          (? (compose not (curry equal? 'ite))))
                     arguments)))))
  (lambda (input-syntax)
    (syntax-case input-syntax ()
      ((_ function arguments)
       (syntax (cons function arguments))))))

(pretty-print-current-style-table
 (pretty-print-extend-style-table
  (pretty-print-current-style-table)
  (list 'and 'or '=> 'ite 'declare-datatype 'forall 'define-fun)
  (list 'and 'and 'and 'and 'define 'define 'define-fun-rec)))

(struct Rule (name formals body) #:transparent)

#;(struct Tip (tests actuals*) #:transparent)

(struct Fun (name formals domains range body) #:transparent)

#|
`nbody` is short for normalized body
|#
(struct FunRec (name formals domains measured? range body nbody machine)
  #:transparent)

(struct Function (original unfolded desugared asserted depth) #:transparent)
(struct And (subgoals) #:transparent)
(struct Or (subgoals) #:transparent)
(struct Goal (latent active used-strats body) #:transparent)

(struct NewGoal (formals domains body) #:transparent)

(define datatypes null)
(define functions null)
(define goal null)
(define goal-point null)

(define new-datatypes null)
(define new-functions null)
(define new-environment null)
(define new-goal null)
(define new-goal-point null)

(define extra (box ""))
(define extra-asserts null)
(define counter (box 0))

(define (ite-helper test-expression then-expression else-expression)
  (match test-expression
    ('true
     then-expression)
    ('false
     else-expression)
    (_
     (list 'ite test-expression then-expression else-expression))))

(define (goal-at-point (g goal) (p goal-point))
  (match p
    ('()
     g)
    (`(,n . ,ns)
     (match g
       ((And gs)
        (goal-at-point (list-ref gs n) ns))
       ((Or gs)
        (goal-at-point (list-ref gs n) ns))))))

(define (update-goal-at-point-helper g^ g p)
  (match p
    ('()
     g^)
    (`(,n . ,ns)
     (match g
       ((And gs)
        (And (list-update 
              gs n
              (lambda (g^^)
                (update-goal-at-point-helper
                 g^ g^^ ns)))))
       ((Or gs)
        (Or (list-update
             gs n
             (lambda (g^^)
               (update-goal-at-point-helper
                g^ g^^ ns)))))))))

(define (update-goal-at-point g^)
  (set! goal (update-goal-at-point-helper g^ goal goal-point)))

(define (repl)
  (define h (Env--goals-hist env))
  
  (cond [(pair? h)
         (define goals (cdr (first h)))
         (if (andmap (lambda (e) (equal? 'true (Goal-concl e))) goals)
             (printf "0 goals -> ")
             (printf "~a goals -> " (length (cdr (first h)))))]
        [else (display "0 goals -> ")])
  (define-values (r cpu real gc)
    (let ((command (read)))
      (time-apply
       (thunk
        (with-handlers ([exn:fail? (lambda (e)
                                     (eprintf "Error in handling command\n")
                                     ((error-display-handler) (exn-message e) e))])
          (match command
            [`(send-to-solver ,v ...)
             (define r (apply send-to-solver v))
             (printf "solver result:\n")
             (pretty-print r)]
            ((list 'set-timeout n)
             (timeout n))
            ((list 'get-timeout)
             (printf "[timeout] ~a~n" (timeout)))
            ((? eof-object?)
             (repl-reset)
             #f)
            ((or (list 'automatic) (list 'automatic (? number?)))
             (define n (if (pair? (cdr command)) (second command) 20))
             (match-define (Tuple status hist) (automatic #:gas n))
             (match status
               ('out-of-gas
                (displayln "[out of gas]"))
               ('success
                (displayln "[success]"))
               ('failure
                (displayln "[failure]")))
             (for ((entry hist))
               (match entry
                 ('(elim-destrs)
                  (displayln '(eliminate-destructors)))
                 ('(repl-prove)
                  (displayln '(prove)))
                 (_
                  (displayln entry)))))
            ((list 'suggest)
             (define schemes
               (suggest))
             (displayln "[induction schemes in descending order of score,]")
             (displayln "[discarding spent schemes                       ]")
             (for ((scheme schemes)
                   (index (range 1 (+ (length schemes) 1)))
                   #:do ((define calls (Scheme-calls scheme))))
               (printf "~a. ~a[~a]  ~a" index (first calls) (Scheme-score scheme)
                       (if (pair? (rest calls)) "SUBSUMES  " ""))
               (newline)))
            ((list 'collect-Schemes)
             (let ((schemes (collect-Schemes)))
               (for ((scheme schemes)
                     (scheme-number (range (length schemes))))
                 (Scheme-displayln scheme)
                 (unless (equal? scheme-number (- (length schemes) 1))
                   (newline)))))
            ((list 'subsumes? call2 call1)
             (displayln (subsumes? (Call-Scheme call2) (Call-Scheme call1))))
            ((list 'new-load file)
             (set! new-datatypes null)
             (set! new-functions null)
             (set! new-environment null)
             (set! new-goal null)
             (set! new-goal-point null)
             (new-load file))
            ((list 'new-print)
             (new-print))
            ((list 'Call-changeables call)
             (displayln (Call-changeables call)))
            ((list 'Call-unchangeables call)
             (displayln (Call-unchangeables call)))
            ((list 'Call-applicable? call)
             (displayln (Call-applicable? call)))
            ((list 'Call-scheme call)
             (let* ((cases (Call-scheme call))
                    (num-cases (length cases)))
               (for ((case/single cases)
                     (idx (range num-cases)))
                 (printf "[case ~a]~n" idx)
                 (for ((test (Tip-tests case/single)))
                   (displayln test))
                 (for ((substn (Tip-actuals* case/single)))
                   (display ":P[")
                   (for ((tuple-or-sep (intersperse substn ",")))
                     (if (string? tuple-or-sep)
                         (display tuple-or-sep)
                         (printf "~a/~a" (cdr tuple-or-sep)
                                 (car tuple-or-sep))))
                   (display "]")
                   (newline))
                 (unless (equal? idx (- num-cases 1))
                   (newline)))))
            ((list 'induct call)
             (induct call))
            ((list 'add-prem prem)
             (update-Env--goals-hist! env
                                      (lambda (goals-hist)
                                        (match-let (((Tuple curs goals) (first goals-hist)))
                                          (let ((goals^ (list-update
                                                         goals curs
                                                         (lambda (goal)
                                                           (struct-copy
                                                            cheesecake-Goal goal
                                                            (prems (:: prem (Goal-prems goal))))))))
                                            (:: (Tuple curs goals^) goals-hist))))))
            ((list 'forward)
             (match-let (((:: (Tuple cursor goals) rest--goals-hist)
                          (Env--goals-hist env)))
               (when (< cursor (- (length goals) 1))
                 (set-Env--goals-hist! env (:: (Tuple (+ cursor 1) goals)
                                               rest--goals-hist)))))
            ((list 'backward)
             (match-let (((:: (Tuple cursor goals) rest--goals-hist)
                          (Env--goals-hist env)))
               (when (> cursor 0)
                 (set-Env--goals-hist! env (:: (Tuple (- cursor 1) goals)
                                               rest--goals-hist)))))
            ((list (or 'elim-destrs 'eliminate-destructors))
             (expr--elim-destrs)
             ;; continue, return value is for other clients
             (void))
            ((list 'new-print-machine name)
             (new-print-machine name))
            ((list 'load file)
             (repl-reset)
             (repl-load file))
            ((list 'undo)
             (repl-undo))
            ((list 'start)
             (repl-reset)
             (void))
            ((list 'print-tips)
             (repl-print-tips))
            ((list 'print-indn)
             (repl-print-indn))
            ((list 'print-goal)
             (repl-print-goal))
            ((list 'print--goals-hist)
             (repl--print--goals-hist))
            ((list 'print--unsat-core)
             (print--unsat-core))
            ('(induct)
             (induct))
            ('(up)
             (up))
            ('(down)
             (down))
            ('(left)
             (left))
            ('(right)
             (right))
            ((list (or 'repl-prove 'prove))
             (unless (repl-prove)
               (displayln "[unknown/sat]")))
            ((list 'exit)
             (repl-reset))
            ('(cleanup)
             (cleanup))
            ('(disembowel)
             (disembowel))
            ('(auto)
             (auto))
            ('(push)
             (display "-> ")
             (let ((form (read)))
               (set! 
                extra-asserts 
                (append
                 extra-asserts
                 `(,form)))))
            ('(pop)
             (when (pair? extra-asserts)
               (set!
                extra-asserts
                (take
                 extra-asserts
                 (- (length extra-asserts) 1)))))
            ('(desugar)
             (match (goal-at-point)
               ((Goal l a us b)
                (update-goal-at-point
                 (Goal l a us (lift-ites (desugar-2 b)))))
               (_
                (void))))
            ('(evaluate)
             (match (goal-at-point)
               ((Goal l a us b)
                (update-goal-at-point
                 (Goal l a us (evaluate b))))
               (_
                (void))))
            ('(identify)
             (match (goal-at-point)
               ((Goal l a us b)
                (match-let
                    (((cons frmls newb) (identify counter (map first (append l a)) b)))
                  (when frmls
                    (let ((newl (foldr (lambda (x acc) (if (member x l) acc (cons x acc))) l frmls)))
                      (update-goal-at-point (Goal newl a us newb))))))))
            ('(simplify)
             (z3simplify))
            ('(qe)
             (z3qe))
            ('(fake-cnf)
             (match (goal-at-point)
               ((Goal latent active strats body)
                (update-goal-at-point
                 (Goal latent active strats (fake-cnf body))))
               (_
                (void))))
            ('(split)
             (match (goal-at-point)
               ((Goal latent active strats `(and . ,xs))
                (let ((subgoals (map (curry Goal latent active strats) xs)))
                  (update-goal-at-point (And subgoals))))
               (_
                (void))))
            ('(patterns)
             (let ((g (goal-at-point)))
               (match g
                 ((Goal active latent strats body)
                  (update-goal-at-point (Goal active latent strats (patterns body))))
                 (_
                  (void)))))
            #;(`(timeout ,n)
               (set! timeout n))
            ('(fail)
             (update-goal-at-point (Goal '() '() '() 'false)))
            ('(instantiate)
             (instantiate))
            ((list 'example0)
             (set-Env--goals-hist! env
                                   (list
                                    (Tuple
                                     0
                                     (list
                                      (cheesecake-Goal
                                       (list 'v)
                                       (list 'Value)
                                       (list '(forall ((v Value))
                                                      (! (=> (is-cons v)
                                                             (and (>= (size (car v)) 0)
                                                                  (>= (size (cdr v)) 0)))
                                                         :pattern ((is-cons v)))))
                                       (list '(not (is-nil v))
                                             '(is-cons v)
                                             '(is-int (car v))
                                             '(not (is-nil (cdr v)))
                                             '(is-cons v)
                                             '(is-int (car v))
                                             '(is-cons (cdr v))
                                             '(is-int (car (cdr v)))
                                             '(< (unint (car v)) (unint (car (cdr v)))))
                                       '(< (size (cdr v)) (size v))))))))
            (c (printf "Unknown command ~a\n" c)))))
       null)))
  (match r
    [(list (? values r))
     (printf "last command took ~a ms\n" real)
     (repl)]
    [_
     (printf "last command took ~a ms\n" real)
     (void)]))

#|
`subexpression?` returns `#t` if the symbol `variable` is a subexpression of
`expression`
|#
(define (subexpression? expression variable)
  (let ((recur (lambda (expression)
                 (subexpression? expression variable))))
    (match expression
      ((? integer?)
       #f)
      ((? symbol?)
       (equal? expression variable))
      ((list 'ite test-expression
             then-expression
             else-expression)
       (or (recur test-expression)
           (recur then-expression)
           (recur else-expression)))
      ((cons function arguments)
       (ormap recur arguments)))))

(define (expression-substitute expression actuals formals)
  (substitute-_*-with-_*-in-_ formals actuals expression))

(define (rewrite-rules-ref rewrite-rules name)
  (match rewrite-rules
    ((list)
     #f)
    ((cons (and rule (Rule rule-name _ _)) rewrite-rules)
     (if (equal? rule-name name)
         rule
         (rewrite-rules-ref rewrite-rules name)))))

(define (expression-rewrite expression rewrite-rules)
  (let ((recur (curryr expression-rewrite rewrite-rules)))
    (match expression
      ((? integer?)
       expression)
      ((? symbol?)
       expression)
      ((list 'ite test-expression
             then-expression
             else-expression)
       (list 'ite (recur test-expression)
             (recur then-expression)
             (recur else-expression)))
      ((cons function arguments)
       (match (rewrite-rules-ref rewrite-rules function)
         (#f
          (cons function (map recur arguments)))
         ((Rule _ formals body)
          (recur (expression-substitute body arguments formals))))))))

(define invocation-arguments cdr)
(define invocation-function car)

(define (expression->tips expression expression-invocations)
  (letrec
      ((stack->tips
        (lambda (stack accumulator)
          (match stack
            ((list)
             accumulator)

            ((:: (tuple tests expression) stack)
             (match expression
               ((? integer?)
                (stack->tips stack accumulator))

               ((? symbol?)
                (stack->tips stack accumulator))

               ((ite test-expression
                     then-expression
                     else-expression)
                (let ((test-invocations
                       (expression-invocations test-expression)))
                  (if (set-empty? test-invocations)
                      (let ((then-tests (:: test-expression tests))
                            (else-tests (:: (negate test-expression) tests)))
                        (stack->tips
                         (:: (tuple then-tests then-expression)
                             (:: (tuple else-tests else-expression)
                                 stack))
                         accumulator))
                      (let ((tip (Tip (reverse tests)
                                      (set-map test-invocations
                                               invocation-arguments))))
                        (stack->tips stack (:: tip accumulator))))))

               ((invoke function arguments)
                (let ((invocations (expression-invocations expression)))
                  (if (set-empty? invocations)
                      (stack->tips stack accumulator)
                      (let ((tip (Tip (reverse tests)
                                      (set-map invocations
                                               invocation-arguments))))
                        (stack->tips stack (:: tip accumulator))))))))))))
    (stack->tips (list (tuple null expression)) null)))

(define (expression-invocations expression names)
  (letrec
      ((helper
        (lambda (stack accumulator)
          (match stack
            ((list)
             accumulator)

            ((:: expression stack)
             (match expression
               ((? integer?)
                (helper stack accumulator))

               ((? symbol?)
                (helper stack accumulator))

               ((ite test-expression
                     then-expression
                     else-expression)
                (helper (:: test-expression
                            (:: then-expression
                                (:: else-expression stack)))
                        accumulator))

               ((invoke function arguments)
                (if (member function names)
                    (helper (append arguments stack)
                            (set-add accumulator expression))
                    (helper (append arguments stack)
                            accumulator)))))))))
    (helper (list expression) (set))))

(define (expression->safety-goals expression)
  (letrec ((helper (lambda (stack accumulator)
                     (match stack
                       ((list)
                        accumulator)

                       ((:: expression stack)
                        (match expression
                          ((invoke 'car (list expression))
                           (helper (:: expression stack)
                                   (:: (invoke 'is-cons (list expression))
                                       accumulator)))

                          ((invoke 'cdr (list expression))
                           (helper (:: expression stack)
                                   (:: (invoke 'is-cons (list expression))
                                       accumulator)))

                          ((invoke 'unbool (list expression))
                           (helper (:: expression stack)
                                   (:: (invoke 'is-bool (list expression))
                                       accumulator)))

                          ((invoke 'unint (list expression))
                           (helper (:: expression stack)
                                   (:: (invoke 'is-int (list expression))
                                       accumulator)))
                          
                          ((invoke function arguments)
                           (helper (append arguments stack) accumulator))

                          (_
                           (helper stack accumulator))))))))
    (helper (list expression) null)))

(define (actuals->goal actuals formals measure relation)
  (let* ((actuals-measure (expression-substitute measure actuals formals))
         (measure-goal (expression-substitute
                        relation (list actuals-measure measure) '(x y)))
         (safety-goals (append-map expression->safety-goals actuals)))
    (:: measure-goal safety-goals)))

(define (tip-revise tip formals domains measure relation definitions)
  (match-let (((Tip tests actuals*) tip)
              (constants (map cons formals domains)))
    (match (prove definitions constants tests 'false)
      ((tuple 'sat _)
       (let* ((actuals->goal_staged (curryr actuals->goal formals measure
                                            relation))
              (goal (invoke 'and (append-map actuals->goal_staged actuals*))))
         (match (prove definitions constants tests goal)
           ((tuple 'sat _)
            (error "tip-revise: sat"))

           ((tuple 'unsat core)
            (Tip core actuals*)))))
      
      ((tuple 'unsat _)
       #f))))

(define (list_2 x y)
  (list x y))

(define (environment->definitions environment)
  (let ((environment (filter FunRec? environment)))
    (map (match-lambda
           ((FunRec name formals domains _ range _ nbody _)
            (list 'define-fun-rec name (map list_2 formals domains) range
                  nbody)))
         environment)))

(define (funrec->machine partial-funrec measure relation environment)
  (match-let*
      (((FunRec name formals domains _ _ _ nbody _) partial-funrec)
       (expression-invocations_staged (curryr expression-invocations
                                              (list name)))
       (tips (expression->tips nbody expression-invocations_staged))
       (definitions (cons
                     '(define-fun-rec size ((v Value)) Int
                        (ite (is-cons v)
                             (+ 1 (size (car v)) (size (cdr v)))
                             0))
                     (environment->definitions environment)))
       (tip-revise_staged (curryr tip-revise formals domains measure relation
                                  definitions)))
    (foldl (lambda (tip accumulator)
             (let ((?revised-tip (tip-revise_staged tip)))
               (if ?revised-tip
                   (:: ?revised-tip accumulator)
                   accumulator)))
           null tips)))

(define (envrules-add envrules form)
  (match-let (((tuple environment rules) envrules))
    (match form

      ((list 'define-fun name (list (list formals domains) ...) range
             body)
       (printf "[environment+] ~a~n" name)
       (tuple (:: (Fun name formals domains range body) environment)
              (:: (Rule name formals body) rules)))

      ((list 'define-fun-rec name (list (list formals domains) ...) range
             body
             (list ':measure measure)
             (list ':relation relation))
       (let* ((measured (map (curry subexpression? measure) formals))
              (nbody (expression-normalize
                      (expression-desugar
                       (expression-rewrite body rules))))
              (new-measure (expression-rewrite measure rules))
              (new-relation (expression-rewrite relation rules))
              (partial-funrec (FunRec name formals domains measured range
                                      body nbody 'TODO))
              (tentative-environment (:: partial-funrec environment))
              (machine (funrec->machine partial-funrec new-measure new-relation
                                        tentative-environment)))
         (printf "[environment+] ~a~n" name)
         (tuple (:: (FunRec name formals domains measured range
                            body nbody machine)
                    environment)
                rules)))

      ((list 'prove (list 'forall (list (list formals domains) ...) body))
       (set! new-goal (NewGoal formals domains body))
       envrules))))

(define (new-load file)
  (match-let*
      ((forms (with-input-from-file file
                (thunk (port->list read))))
       ((tuple environment _) (foldl (lambda (form envrules)
                                       (envrules-add envrules form))
                                     (tuple null null) forms)))
    (set! new-environment environment)))

(define (environment-ref environment name)
  (findf (lambda (function)
           (and (FunRec? function)
                (equal? (FunRec-name function) name)))
         environment))

#;(define (funrec-applies? funrec invocation)
  (match-let*
      (((FunRec name formals _ measured? _ _ _ machine) funrec)
       (indscm-tips (map (match-lambda
                           ((Tip tests actuals*)
                            (indscm-Tip tests actuals*)))
                         machine))
       (indscm-machine (indscm-Machine name (map cons formals measured?)
                                       indscm-tips)))
    (applies? indscm-machine invocation)))

(define (goal-induct goal tests* substitutions* accumulator)
  (match* (tests* substitutions*)
    (((:: tests tests*)
      (:: substitutions substitutions*))
     (let ((goal^ (NewGoal
                   (NewGoal-formals goal)
                   (NewGoal-domains goal)
                   (invoke
                    '=> (append tests
                                (map (match-lambda
                                       ((list (tuple formals actuals) ...)
                                        (expression-substitute
                                         (NewGoal-body goal) actuals formals)))
                                     substitutions)
                                (list (NewGoal-body goal)))))))
       (goal-induct goal tests* substitutions* (:: goal^ accumulator))))

    (((list)
      (list))
     (And accumulator))))

#;(define (new-induct invocation)
  (match-let*
      (((FunRec name formals _ measured? _ _ _ machine)
        (environment-ref new-environment (invocation-function invocation)))
       (indscm-tips (map (match-lambda
                           ((Tip tests actuals*)
                            (indscm-Tip tests actuals*)))
                         machine))
       (indscm-machine (indscm-Machine name (map cons formals measured?)
                                       indscm-tips))
       ((indscm-Machine _ _ (list (indscm-Tip tests* substitutions*) ...))
        (make-scheme indscm-machine invocation))
       ((NewGoal goal-formals goal-domains body) new-goal)
       (accumulator (list (NewGoal
                           goal-formals goal-domains
                           (list '=>
                                 (list 'not (cons 'or (map (curry cons 'and) tests*)))
                                 body)))))
    (set! new-goal (goal-induct new-goal tests* substitutions* accumulator))))

#;(define (new-show-inductions)
  (let* ((names (map FunRec-name (filter FunRec? new-environment)))
         (goal-body (NewGoal-body new-goal))
         (invocations (expression-invocations goal-body names)))
    (for/set ((invocation invocations))
      (let ((funrec (environment-ref new-environment
                                     (invocation-function invocation))))
        (when (funrec-applies? funrec invocation)
          (printf "(induct ~a)~n" invocation))))))

(define (load file)
  (match-let*-values
      (((port) (open-input-file file))
       ((statements) (begin0
                         (port->list read port)
                       (close-input-port port)))

       ;; inline all 'define-fun' forms
       ((statements) (eliminate-define-fun statements))

       ;; turn each 'define-funs-rec' form into a 'define-fun-rec' form using an
       ;; additional flag argument
       ((statements) (eliminate-define-funs-rec statements))

       ((datatype-declarations statements) (partition declare-datatype?
                                                      statements))

       ((function-definitions (cons assertion _)) (partition define-fun-rec?
                                                             statements))

       ;; desugar each function definition, normalize it, and compute its depth
       ((function-structs) (map make-Function function-definitions)))

    (set! datatypes datatype-declarations)
    (set! functions function-structs)
    (set! goal (make-Goal assertion))))

(define (declare-datatype? statement)
  (match statement
    (`(declare-datatype . ,_) #t)
    (_                        #f)))

(define (define-fun-rec? statement)
  (match statement
    (`(define-fun-rec . ,_) #t)
    (_                      #f)))

(define (make-Function original)
  (let* ((desugared (normalize original))
         (asserted (define-fun-rec->assert desugared))
         (depth (depth_definition original)))
    (Function original original desugared asserted depth)))

(define (make-Goal statement)
  (match statement
    (`(assert (not (forall ,formals ,body)))
     (Goal formals '() '() body))))

(define (new-print)
  (letrec ((goal->sexps (match-lambda
                          ((NewGoal formals domains body)
                           (list (list 'forall (map list_2 formals domains) body)))
                          
                          ((And goals)
                           (append-map goal->sexps goals)))))
    (for ((sexp (goal->sexps new-goal)))
      (pretty-display sexp))))

(define (intersperse lst elt (acc (list)))
  (match lst
    ((list)
     (list))
    ((list elt^)
     (reverse (cons elt^ acc)))
    ((cons elt^ lst)
     (intersperse lst elt (cons elt (cons elt^ acc))))))

(define (new-print-machine name)
  (let ((?funrec (environment-ref new-environment name)))
    (when ?funrec
      (for ((tip (FunRec-machine ?funrec)))
        (match-let (((Tip tests actuals*) tip))
          (for ((sexp (append (intersperse tests '∧)
                              (list '⇒)
                              (intersperse actuals* '|,|))))
            (display sexp)
            (display " ")))
        (newline)))))

(define (goal-print (offset "") (g (goal-at-point)))
  (match g
    ((Goal l a us b)
     (displayln (string-append offset (format "latent: ~a" l)))
     (displayln (string-append offset (format "active: ~a" a)))
     (displayln (string-append offset (format "used strategies: ~a" us)))
     (displayln (string-append offset "body:"))
     (displayln (string-join (map (curry string-append offset) (rest-format b)) "\n")))
    ((And gs)
     (displayln (string-append offset "** AND **"))
     (for ((g gs))
       (goal-print (string-append offset "    ") g))
     (displayln (string-append offset "*********")))
    ((Or gs)
     (displayln (string-append offset "** OR **"))
     (for ((g gs))
       (goal-print (string-append offset "    ") g))
     (displayln (string-append offset "********")))))

(define (lookup name fs)
  (match fs
    ('() (error (format "lookup: ~a not found" name)))
    (`(,(and f (Function _ _ d _ _)) . ,fs^)
     (match d
       (`(define-fun-rec ,name^ . ,_)
        (if (equal? name name^)
            f
            (lookup name fs^)))))))

(define (formals-remove formals var)
  (match formals
    ((list)
     (list))
    ((cons (list |var'| sort) formals)
     (if (equal? var |var'|)
         formals
         (cons (list |var'| sort) (formals-remove formals var))))))

(define make-goals list)
(define make-goal list)
(define join-goals append)
(define join-goal append)

(define (negate p)
  (match p
    (`(not ,p^)
     p^)
    (_ 
     `(not ,p))))

(define (sanitize s)
  (match s
    (`(forall () ,body)
     body)
    (_
     s)))

(define (smt)
  (match-let*
      (((Goal latent active us body) (goal-at-point))
       (opts `((set-option :smt.auto_config false)
               (set-option :smt.mbqi false)
               (set-option :smt.ematching true)
               (set-option :timeout ,timeout)))
       (types datatypes)
       (funs (append-map Function-asserted functions))
       (consts (map (curry cons 'declare-const) (append latent active)))
       (claim `((assert (not ,body))))
       (check '((check-sat-using (then simplify qe-light snf smt))))
       (all (append opts types funs consts extra-asserts claim check))
       (outh (open-output-file #:exists 'truncate "query.smt2"))
       (_ (for ((form all)) (displayln form outh) (newline outh)))
       (_ (close-output-port outh))
       (z3outh (open-output-string))
       (_ (parameterize ((current-output-port z3outh))
            (system "z3 query.smt2" #:set-pwd? #t)))
       (z3out (get-output-string z3outh))
       (z3res (port->list read (open-input-string z3out))))
    (if (equal? z3res '(unsat))
        (update-goal-at-point (Goal '() '() us 'true))
        (void))))

(define (z3simplify)
  (match-let*
      (((Goal latent active us body) (goal-at-point))
       (opts `((set-option :smt.auto_config false)
               (set-option :smt.mbqi false)
               (set-option :smt.ematching true)
               (set-option :timeout ,timeout)))
       (types datatypes)
       (funs (map (compose first Function-asserted) functions))
       (consts (map (curry cons 'declare-const) (append latent active)))
       (claim `((assert ,body)))
       (cmd '((apply simplify)))
       (all (append opts types funs consts claim cmd))
       (outh (open-output-file #:exists 'truncate "simp.smt2"))
       (_ (for ((form all)) (displayln form outh) (newline outh)))
       (_ (close-output-port outh))
       (z3outh (open-output-string))
       (_ (parameterize ((current-output-port z3outh))
            (system "z3 simp.smt2" #:set-pwd? #t)))
       (z3out (get-output-string z3outh))
       (z3res (port->list read (open-input-string z3out))))
    (match z3res
      (`((goals (goal . ,other)))
       #:when (> (length other) 3)
       (let* ((asserts (take other (- (length other) 4)))
              (asserts (map remove-let asserts))
              (asserts (map rewrite-is asserts))
              (newb (if (equal? (length asserts) 1)
                        (car asserts)
                        `(and . ,asserts))))
         (update-goal-at-point
          (Goal latent active us newb))))
      (_
       (void)))))

(define (z3qe)
  (match-let*
      (((Goal latent active us body) (goal-at-point))
       (opts `((set-option :smt.auto_config false)
               (set-option :smt.mbqi false)
               (set-option :smt.ematching true)
               (set-option :timeout ,timeout)))
       (types datatypes)
       (funs (map (compose first Function-asserted) functions))
       (claim `((assert (forall ,(append latent active) ,body))))
       (cmd '((apply qe-light)))
       (all (append opts types funs claim cmd))
       (outh (open-output-file #:exists 'truncate "simp.smt2"))
       (_ (for ((form all)) (displayln form outh) (newline outh)))
       (_ (close-output-port outh))
       (z3outh (open-output-string))
       (_ (parameterize ((current-output-port z3outh))
            (system "z3 simp.smt2" #:set-pwd? #t)))
       (z3out (get-output-string z3outh))
       (z3res (port->list read (open-input-string z3out))))
    (match z3res
      (`((goals (goal . ,other)))
       #:when (> (length other) 3)
       (match-let*
           ((asserts (take other (- (length other) 4)))
            (asserts (map remove-let asserts))
            (asserts (map rewrite-is asserts))
            ((cons quants asserts) (foldr
                                    (match-lambda**
                                     ((`(forall ,frmls ,body) (cons quants asserts))
                                      (cons (append frmls quants) `(,body . ,asserts)))
                                     ((e (cons quants asserts))
                                      (cons quants `(,e . ,asserts))))
                                    (cons '() '())
                                    asserts))
            ((cons newl newa) (foldr
                               (match-lambda**
                                ((frml (and (cons newl newa) acc))
                                 (if (member frml active)
                                     (if (member frml newa)
                                         acc
                                         (cons newl `(,frml . ,newa)))
                                     (if (member frml newl)
                                         acc
                                         (cons `(,frml . ,newl) newa)))))
                               (cons '() '())
                               quants))
            (newb (if (equal? (length asserts) 1)
                      (car asserts)
                      `(and . ,asserts))))
         (update-goal-at-point
          (Goal newl newa us newb))))
      (_
       (void)))))

(define (remove-let e)
  (match e
    ((? integer?) e)
    ((? symbol?) e)
    (`(forall ,frmls ,body)
     `(forall ,frmls ,(remove-let body)))
    (`(forall ,frmls (! ,body . ,meta))
     `(forall ,frmls (! ,(remove-let body) . ,meta)))
    (`(let ((,vars ,vals) ...) ,body)
     (remove-let 
      (substitute-_*-with-_*-in-_
       vars vals body)))
    (`(,fun . ,args)
     `(,fun . ,(map remove-let args)))
    (_
     e)))

(define (goal-atomic-true? g)
  (and (Goal? g)
       (equal? (Goal-body g) 'true)))

(define (goal-atomic-false? g)
  (and (Goal? g)
       (equal? (Goal-body g) 'false)))

(define (cleanup-helper g)
  (match g
    ((? Goal?)
     g)
    ((And gs)
     (let*
         ((gs (map cleanup-helper gs))
          (gs (filter (compose not goal-atomic-true?) gs))
          (fg (memf goal-atomic-false? gs)))
       (or (and fg (first fg))
           (match gs
             ('()
              (Goal '() '() '() 'true))
             (`(,g0)
              g0)
             (_
              (And gs))))))
    ((Or gs)
     (let*
         ((gs (map cleanup-helper gs))
          (gs (filter (compose not goal-atomic-false?) gs))
          (tg (memf goal-atomic-true? gs)))
       (or (and tg (first tg))
           (match gs
             ('()
              (Goal '() '() '() 'false))
             (`(,g0)
              g0)
             (_
              (Or gs))))))))

(define (cleanup)
  (set! goal (cleanup-helper goal))
  (set! goal-point '()))

#;(define (induct)
  (match-let* 
      (((Goal latent active used-strategies body) (goal-at-point))
       (function-names (map (match-lambda
                              ((Function _ _ `(define-fun-rec ,name ,_ ,_
                                                ,_) _ _)
                               name)) functions))

       ;; gather all calls to recursive functions in the body of the goal
       (calls (calls-to-_-in-_ function-names body))

       ;; turn each recursive call -- which is assumed to have at most two
       ;; arguments -- into a template, by substituting the final argument with
       ;; the placeholder symbol `VARIABLE`
       ;; pair up every template with every latent variable, and for each pair
       ;; substitute the latent variable for the placeholder symbol `VARIABLE`
       ;; in the template
       (strategies (remove-duplicates
                    (map
                     (match-lambda
                       ((list `(,f ,@es ,_) name)
                        `(,f ,@es ,name)))
                     (cartesian-product
                      calls (map (match-lambda
                                   ((list name _)
                                    name)) latent))))))

    (printf "_Strategies_~n")
    (for ((strategy strategies))
      (printf "~a~n" strategy))

    (update-goal-at-point
     (Or
      (map
       (match-lambda
         ((cons f es)
          (match-let*
              (((Function
                 _ _
                 `(define-fun-rec ,_ ,(list `(,formals ,_) ...) ,range
                    ,body_f)
                 _ _) (lookup f functions))
               (body_f (substitute-_*-with-_*-in-_ formals es body_f))
               (induction-variable (last es))
               (|latent'| (formals-remove latent induction-variable))
               (subgoals (make-subgoals
                          f body_f es (append |latent'| active) body)))
            (And
             (map 
              (lambda (subgoal)
                (Goal
                 |latent'|
                 (append (filter
                          (match-lambda
                            ((list name _)
                             (equal? name induction-variable)))
                          latent)
                         active)
                 (cons f used-strategies)
                 (if (equal? subgoal 'true)
                     'true
                     (cons '=> subgoal))))
              subgoals)))))
       strategies)))
    (cleanup)))

(define (induct_1)
  (match-let* 
      (((Goal latent active used-strategies body) (goal-at-point))
       (function-names (map (match-lambda
                              ((Function _ _ `(define-fun-rec ,name ,_ ,_
                                                ,_) _ _)
                               name)) functions))
       
       ((and calls (cons `(,f ,@es ,_) _)) (calls-to-_-in-_ function-names
                                                            body))

       (strategies (remove-duplicates
                    (map (match-lambda
                           ((list name _)
                            `(,f ,@es ,name))) latent)))

       (callee-names (remove-duplicates
                      (map (match-lambda
                             ((cons f _)
                              f)) calls)))

       (callee-depths (map (lambda (callee-name)
                             (match-let
                                 (((Function _ _ _ _ depth) (lookup callee-name
                                                                    functions)))
                               depth))
                           callee-names))

       (depths-lcm (foldl lcm 1 callee-depths))

       ((Function _ _ definition_f _ depth_f) (lookup f functions))

       ((and definition_f
             `(define-fun-rec ,_ ,(list `(,formals ,_) ...) ,_
                ,body_f)) (normalize
                           (unfold definition_f
                                   (- (quotient depths-lcm depth_f) 1)))))

    (printf "_Strategies_~n")
    (for ((strategy strategies))
      (printf "~a~n" strategy))
    (printf "_Unfoldings_ ~a~n" (- (quotient depths-lcm depth_f) 1))
    (printf "_Body_~n")
    (pretty-print definition_f)
    
    (update-goal-at-point
     (Or
      (map
       (match-lambda
         ((cons _ (and es (list _ ... induction-variable)))
          (match-let*
              ((body_f (substitute-_*-with-_*-in-_ formals es body_f))
               (|latent'| (formals-remove latent induction-variable))
               (subgoals (make-subgoals
                          f body_f es (append |latent'| active) body)))
            (And
             (map 
              (lambda (subgoal)
                (Goal
                 |latent'|
                 (append (filter
                          (match-lambda
                            ((list name _)
                             (equal? name induction-variable)))
                          latent)
                         active)
                 (cons f used-strategies)
                 (if (equal? subgoal 'true)
                     'true
                     (cons '=> subgoal))))
              subgoals)))))
       strategies)))
    (cleanup)))

(define (make-subgoals name_f body_f vars_ind vars_const body_g)
  (match body_f
    ((? integer?)
     (make-goals (make-goal body_g)))

    ((? symbol?)
     (make-goals (make-goal body_g)))

    ((cons function arguments)
     #:when (not (equal? function 'ite))
     (let ((calls (calls-to-_-in-_ (list name_f) body_f)))
       (if (pair? calls)
           (let* ((fresh-vars_const (map (match-lambda
                                           ((list name sort)
                                            (list (next counter) sort)))
                                         vars_const))
                  (hypotheses (map
                               (match-lambda
                                 ((cons _ actuals)
                                  (sanitize
                                   `(forall ,fresh-vars_const
                                      ,(substitute-_*-with-_*-in-_
                                        (append vars_ind
                                                (map first vars_const))
                                        (append actuals
                                                (map first fresh-vars_const))
                                        body_g)))))
                               calls))
                  (result (foldl (lambda (hypothesis conclusion)
                                   (premises-add conclusion hypothesis))
                                 (list body_g) hypotheses)))
             (printf "application ~a yields ~a" body_f result)
             (list result))
           (make-goals (make-goal body_g)))))

    ((list 'ite question answer else)
     (let ((calls_question (calls-to-_-in-_ (list name_f) question)))
       (if (pair? calls_question)
           (let ((calls (calls-to-_-in-_ (list name_f) body_f)))
             (if (pair? calls)
                 (let* ((fresh-vars_const (map (match-lambda
                                                 ((list name sort)
                                                  (list (next counter) sort)))
                                               vars_const))
                        (hypotheses (map
                                     (match-lambda
                                       ((cons _ actuals)
                                        (sanitize
                                         `(forall ,fresh-vars_const
                                            ,(substitute-_*-with-_*-in-_
                                              (append vars_ind
                                                      (map first vars_const))
                                              (append actuals
                                                      (map first
                                                           fresh-vars_const))
                                              body_g)))))
                                     calls)))
                   (list
                    (foldl (lambda (hypothesis conclusion)
                             (premises-add conclusion hypothesis))
                           (list body_g) hypotheses)))
                 (make-goals (make-goal body_g))))
           (let* ((goals_answer (make-subgoals
                                 name_f answer vars_ind vars_const body_g))
                  (goals_answer (map (lambda (goal_answer)
                                       (premises-add goal_answer question))
                                     goals_answer))
                  (goals_else (make-subgoals
                               name_f else vars_ind vars_const body_g))
                  (goals_else (map (lambda (goal_else)
                                     (premises-add goal_else
                                                   (negate question)))
                                   goals_else))
                  (result (append goals_answer goals_else)))
             (for ((goal result))
               (printf "~a~n" goal))
             result))))))

(define (disembowel)
  (displayln (tree-pretty '()))
  (newline)
  (displayln (make-string 80 #\-))
  (newline)
  (if (Goal? (goal-at-point))
    (goal-print)
    (displayln "·"))
  (newline)
  (display (make-string 10 #\-)) 
  (display " assuming ")
  (displayln (make-string 60 #\-))
  (newline)
  (for ((form extra-asserts))
    (displayln
     (string-join 
      (rest-format (second form))
      "\n")))
  (newline)
  (displayln (make-string 80 #\-))
  (newline)
  (displayln (unbox extra))
  (set-box! extra ""))

(define (tree-pretty p (offset "") (g goal))
  (match g
    ((And gs)
     (string-join
      (cons
       (string-append  offset "−− ∧" (if (equal? p goal-point) " (*)" ""))
       (map (lambda (g^ n)
              (tree-pretty
               (append p `(,n))
               (string-append offset "   ")
               g^) )
            gs
            (range 0 (length gs))))
      "\n"))
    ((Or gs)
     (string-join
      (cons
       (string-append  offset "−− ∨" (if (equal? p goal-point) " (*)" ""))
       (map (lambda (g^ n)
              (tree-pretty
               (append p `(,n))
               (string-append offset "   ")
               g^) )
            gs
            (range 0 (length gs))))
      "\n"))    
    ((Or gs)
     (error "undefined"))
    ((Goal _ _ _ 'true)
     (string-append offset "−− ✓" (if (equal? p goal-point) " (*)" "")))
    ((Goal _ _ _ 'false)
     (string-append offset "−− ×" (if (equal? p goal-point) " (*)" "")))
    (_
     (string-append offset "−− G" (if (equal? p goal-point) " (*)" "")))))

(define (premises-add-helper phis phi acc)
  (match phis
    ((cons phi^ phis^)
     (cond
       ((equal? phi phi^)
        (premises-add-helper phis^ 'true (cons phi^ acc)))
       ((equal? (negate phi) phi^)
        'true)
       (else
        (match phi
          (`(is-cons ,e)
           (match phi^
             (`(is-nil ,e^)
              #:when (equal? e e^)
              'true)
             (`(not (is-nil ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ phi acc))
             (`(is-integer ,e^)
              #:when (equal? e e^)
              'true)
             (`(not (is-integer ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ phi acc))
             (_
              (premises-add-helper phis^ phi (cons phi^ acc)))))
          (`(not (is-cons ,e))
           (match phi^
             (`(is-nil ,e^)
              #:when (equal? e e^)
              (premises-add-helper phis^ 'true (cons phi^ acc)))
             (`(not (is-nil ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ `(is-integer ,e) acc))
             (`(is-integer ,e^)
              #:when (equal? e e^)
              (premises-add-helper phis^ 'true (cons phi^ acc)))
             (`(not (is-integer ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ `(is-nil ,e) acc))
             (_
              (premises-add-helper phis^ phi (cons phi^ acc)))))
          (`(is-nil ,e)
           (match phi^
             (`(is-cons ,e^)
              #:when (equal? e e^)
              'true)
             (`(not (is-cons ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ phi acc))
             (`(is-integer ,e^)
              #:when (equal? e e^)
              'true)
             (`(not (is-integer ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ phi acc))
             (_
              (premises-add-helper phis^ phi (cons phi^ acc)))))
          (`(not (is-nil ,e))
           (match phi^
             (`(is-cons ,e^)
              #:when (equal? e e^)
              (premises-add-helper phis^ 'true (cons phi^ acc)))
             (`(not (is-cons ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ `(is-integer ,e) acc))
             (`(is-integer ,e^)
              #:when (equal? e e^)
              (premises-add-helper phis^ 'true (cons phi^ acc)))
             (`(not (is-integer ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ `(is-cons ,e) acc))
             (_
              (premises-add-helper phis^ phi (cons phi^ acc)))))
          (`(is-integer ,e)
           (match phi^
             (`(is-cons ,e^)
              #:when (equal? e e^)
              'true)
             (`(not (is-cons ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ phi acc))
             (`(is-nil ,e^)
              #:when (equal? e e^)
              'true)
             (`(not (is-nil ,e^))
              #:when (equal? e e^)
              (premises-add-helper phis^ phi acc))
             (_
              (premises-add-helper phis^ phi (cons phi^ acc)))))
          (`(not (is-integer ,e))
           (match phi^
             (`(is-cons ,e^)
              #:when (equal? e e^)
              (premises-add-helper phi^ 'true (cons phi^ acc)))
             (`(not (is-cons ,e^))
              #:when (equal? e e^)
              (premises-add-helper phi^ `(is-nil ,e) acc))
             (`(is-nil ,e^)
              #:when (equal? e e^)
              (premises-add-helper phi^ 'true (cons phi^ acc)))
             (`(not (is-nil ,e^))
              #:when (equal? e e^)
              (premises-add-helper phi^ `(is-cons ,e) acc))
             (_
              (premises-add-helper phis^ phi (cons phi^ acc)))))
          (_
           (premises-add-helper phis^ phi (cons phi^ acc)))))))
    ('()
     (match phi
       ('true acc)
       (_     (cons phi acc))))))

(define (premises-add phis phi)
  (if (equal? phis 'true)
      'true
      (match phi
        (`(= ,e1 ,e2)
         #:when (equal? e1 e2)
         phis)
        (`(not (= ,e1 ,e2))
         #:when (equal? e1 e2)
         'true)
        (_
         (premises-add-helper (reverse phis) phi '())))))

(define (up)
  (let ((l (length goal-point)))
    (when (> l 0)
      (set! goal-point (take goal-point (- l 1))))))

(define (down)
  (let ((g (goal-at-point)))
    (when (or (and (And? g)
                   (> (length (And-subgoals g)) 0))
              (and (Or? g)
                   (> (length (Or-subgoals g)) 0)))
      (set! goal-point (append goal-point '(0))))))

(define (left)
  (let ((gpl (length goal-point)))
    (when (and (> gpl 0) (> (list-ref goal-point (- gpl 1)) 0))
      (set! goal-point (list-update goal-point (- gpl 1) (curryr - 1))))))

(define (right)
  (let ((l (length goal-point)))
    (when (> l 0)
      (let* ((p (goal-at-point goal (take goal-point (- l 1))))
             (s (if (And? p) (And-subgoals p) (Or-subgoals p))))
        (when (< (list-ref goal-point (- l 1)) (- (length s) 1))
          (set! goal-point 
                (list-update goal-point (- l 1) (curry + 1))))))))

(define/match (rewrite-is e)
  (((? integer?))
   e)
  (((? symbol?))
   e)
  ((`(forall ,frmls ,body))
   `(forall ,frmls ,(rewrite-is body)))
  ((`((_ is nil) ,x))
   `(is-nil ,(rewrite-is x)))
  ((`((_ is cons) ,x))
   `(is-cons ,(rewrite-is x)))
  ((`((_ is integer) ,x))
   `(is-integer ,(rewrite-is x)))
  ((`(,f . ,xs))
   `(,f . ,(map rewrite-is xs))))

(define (auto)
  (let ((g (goal-at-point)))
    (match g 
      ((Goal _ _ _ 'true)
       (void))
      ((Goal _ _ _ body)
       (smt))
      ((And gs)
       (let ((acts (append
                    `(,down)
                    (add-between
                     (make-list
                      (length gs)
                      auto)
                     right)
                    `(,up))))
         (for ((act acts))
           (act))))
      ((Or gs)
       (let ((acts (append
                    `(,down)
                    (add-between
                     (make-list
                      (length gs)
                      auto)
                     right)
                    `(,up))))
         (for ((act acts))
           (act)))))))

(define (footnote s)
  (set-box! extra (string-append (unbox extra) s)))

(define/match (patterns e)
  (((? integer?))
   e)
  (((? symbol?))
   e)
  ((`(forall ,frmls (! ,body . ,meta)))
   (patterns `(forall ,frmls ,body)))
  ((`(forall ,frmls ,body))
   (let*
       ((new-body (patterns body))
        (names (map (compose second Function-original) functions))
        (calls (calls-to-_-in-_ names new-body))
        (holes (map
                (match-lambda
                  (`(,f ,x ,_)
                   `(,f ,x VARIABLE))
                  (`(,f ,_)
                   `(,f VARIABLE)))
                calls))
        (holes (set->list (list->set holes)))
        (plugs (map first frmls))
        (pats (map
               (match-lambda
                 (`(,hole ,plug)
                  (substitute-_*-with-_*-in-_
                   '(VARIABLE) `(,plug) hole)))
               (cartesian-product holes plugs))))
     `(forall ,frmls (! ,new-body :pattern ,pats))))
  ((`(,f . ,es))
   `(,f . ,(map patterns es))))

(define (subexpressions subes e)
  (match e
    ('nil
     (set-add subes e))
    (`(integer ,n)
     (set-add subes e))
    (`(cons ,e1 ,e2)
     (set-add
      (subexpressions
       (subexpressions
        subes
        e1)
       e2)
      e))
    (`(car ,e^)
     (set-add (subexpressions subes e^) e))
    (`(cdr ,e^)
     (set-add (subexpressions subes e^) e))
    (`(integer-out ,e^)
     (subexpressions subes e^))
    ((? symbol?)
     (set-add subes e))
    (_
     subes)))

(define (typeof ctx v)
  (match ctx
    ('()
     #f)
    (`((,name ,sort) . ,rest)
     (if (equal? name v)
         sort
         (typeof rest v)))))

(define (typecheck ctx e)
  (match e
    ('nil
     #t)
    (`(integer ,n)
     (or (integer? n)
         (equal? (typeof ctx n) 'Int)))
    (`(cons ,e1 ,e2)
     (and (typecheck ctx e1)
          (typecheck ctx e2)))
    (`(car ,e^)
     (typecheck ctx e^))
    (`(cdr ,e^)
     (typecheck ctx e^))
    (`(integer-out ,e^)
     #f)
    ((? symbol?)
     (equal? (typeof ctx e) 'Value))
    (_
     #f)))

(define (instantiate-helper ts e)
  (match e
    ((? symbol?)
     e)
    ((? integer?)
     e)
    (`(forall ,frmls (! ,body . ,meta))
     (instantiate-helper ts `(forall ,frmls ,body)))
    (`(forall ,frmls ,body)
     (let* 
         ((l (length frmls))
          (tss (apply cartesian-product (make-list l ts)))
          (insts (map (lambda (ts) (substitute-_*-with-_*-in-_ (map first frmls) ts body)) tss)))
       `(and . ,insts)))
    (`(,f . ,es)
     `(,f . ,(map (curry instantiate-helper ts) es)))))

(define (instantiate (g (goal-at-point)))
  (match g
    ((Goal latent active strats body)
     (match-let*
         ((user-def-fn-names (map (compose second Function-original) functions))
          ;;(_ (for ((name user-def-fn-names)) (displayln name)))
          (user-def-fn-calls (calls-to-_-in-_ user-def-fn-names body))
          ;;(_ (begin (for ((call user-def-fn-calls)) (displayln call)) (displayln "−−−−−")))
          (user-def-fn-args (set->list (list->set (map (lambda (user-def-fn-call) (last user-def-fn-call)) user-def-fn-calls))))
          ;;(_ (begin (for ((arg user-def-fn-args)) (displayln arg)) (displayln "−−−−−")))
          (candidates (set->list (foldl (lambda (arg acc) (subexpressions acc arg)) (set) user-def-fn-args)))
          ;;(_ (begin (for ((candidate candidates)) (displayln candidate)) (displayln "−−−−−")))
          (well-typed-candidates (filter (curry typecheck (append latent active)) candidates))
          (well-typed-candidates (if (> (length well-typed-candidates) 10) (take well-typed-candidates 10) well-typed-candidates))
          ;;(_ (begin (for ((wtc well-typed-candidates)) (displayln wtc)) (displayln "−−−−−")))
          )
       (update-goal-at-point
        (Goal latent active strats (instantiate-helper well-typed-candidates body)))))
    (_
     (void))))

(define instantiate-example-1
  (Goal '((v3 Value) (v5 Value) (v6 Value) (v7 Value)) '((v2 Value)) '()
  '(=> (is-cons v2)
     (is-nil (car v2))
     (is-cons (cdr v2))
     (is-nil (car (cdr v2)))
     (forall
      ((v123 Value) (v122 Value) (v121 Value) (v120 Value))
      (=> (is-even v123)
          (is-nat_to_nat
           (cons (cons (cdr (cdr v2)) v120) (cons (cons v123 v122) v121)))
          (is-nat v120)
          (is-even (cdr (cdr v2)))
          (not (is-nat v122))
          (is-even_to_nat
           (cons (cons (cdr (cdr v2)) v120) (cons (cons v123 v122) v121)))))
     (is-even v6)
     (is-nat_to_nat (cons (cons v2 v3) (cons (cons v6 v7) v5)))
     (is-nat v3)
     (is-even v2)
     (not (is-nat v7))
     (is-even_to_nat (cons (cons v2 v3) (cons (cons v6 v7) v5))))))

(module+ main
  (repl))

#|
(define (subgoals name fbody vars latent gbody)
  (subgoals-helper name fbody vars latent gbody))

(define (subgoals-helper strategy e formals latent g)
  (match e
    (`(ite ,Q ,A ,E)
     (let ((common 
            (match Q
              (`(,function . ,actuals)
               #:when (equal? function strategy)
               (let ((fresh-latent
                      (foldr
                       (match-lambda**
                        ((`(,variable ,sort) accumulator)
                         `((,(next counter) ,sort) . ,accumulator)))
                       '()
                       latent)))
                 (make-goals
                  (make-goal
                   (sanitize
                    `(forall
                      ,fresh-latent
                      ,(substitute-_*-with-_*-in-_
                        `(,@formals ,@(map first latent))
                        `(,@actuals ,@(map first fresh-latent))
                        g)))
                   g))))
              (_ '()))))
       (join-goals
        (map 
         (lambda (conclusion)
           (foldr (lambda (p acc) (premises-add acc p)) conclusion (join-goal common (make-goal Q))))
         (subgoals-helper strategy A formals latent g))
        (map 
         (lambda (conclusion)
           (foldr (lambda (p acc) (premises-add acc p)) conclusion (join-goal common (make-goal (negate Q)))))
         (subgoals-helper strategy E formals latent g)))))
    (`(,function . ,actuals)
     #:when (equal? function strategy)
     (let ((fresh-latent
            (foldr
             (match-lambda**
              ((`(,variable ,sort) accumulator)
               `((,(next counter) ,sort) . ,accumulator)))
             '()
             latent)))
       (make-goals
        (make-goal
         (sanitize
          `(forall
            ,fresh-latent
            ,(substitute-_*-with-_*-in-_
              `(,@formals ,@(map first latent))
              `(,@actuals ,@(map first fresh-latent))
              g)))))))
    ;; NOTE. What happens if e does not have boolean type?
    (_
     (make-goals (make-goal g)))))

(define (subgoals-helper name fbody vars latent gbody)
  (match fbody
    ((? integer?)
     `((,gbody)))
    ((? symbol?)
     `((,gbody)))
    (`(ite ,q ,a ,e)
     (match-let*
         ((p (match q
               (`(,fun . ,args)
                #:when (equal? fun name)
                (let ((latent^ (foldr
                                (match-lambda**
                                 ((`(,var ,sort) acc)
                                  `((,(next counter) ,sort) . ,acc)))
                                '()
                                latent)))
                  (sanitize
                   `(forall 
                        ,latent^
                      ,(substitute-_*-with-_*-in-_
                        (append vars (map first latent))
                        (append args (map first latent^))
                        gbody)))))
               (_ q)))
          (acs (subgoals-helper name a vars latent gbody))
          (ecs (subgoals-helper name e vars latent gbody)))
       (append (map (curryr premises-add p) acs)
               (map (curryr premises-add (negate p)) ecs))))
    (`(,fun . ,args)
     #:when (equal? fun name)
     (let ((latent^ (foldr
                     (match-lambda**
                      ((`(,var ,sort) acc)
                       `((,(next counter) ,sort) . ,acc)))
                     '()
                     latent)))
       `((,(sanitize
            `(forall 
                 ,latent^
               ,(substitute-_*-with-_*-in-_
                 (append vars (map first latent))
                 (append args (map first latent^))
                 gbody)))
          ,gbody)))
     #;`((,(sanitize
            `(forall ,latent
               ,(substitute-_*-with-_*-in-_ vars args gbody)))
          ,gbody)))
    (`(,fun . ,args)
     `((,gbody)))))
|#
