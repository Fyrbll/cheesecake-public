#lang racket/base

(require
 cheesecake/macros
 cheesecake/structs
 cheesecake/list
 (only-in racket/list first range)
 (only-in racket/match match-let)
 (only-in racket/pretty pretty-print-current-style-table
          pretty-print-extend-style-table pretty-display)
 "./env.rkt"
 racket/match)
(provide
 (all-defined-out))

(pretty-print-current-style-table
 (pretty-print-extend-style-table
  (pretty-print-current-style-table)
  (list 'ite 'and 'or  '=>  'forall '!)
  (list 'and 'and 'and 'and 'when   'and)))

(define (repl-print-goal)
  (match (Env--goals-hist env)
    ['() (printf "no goals\n")]
    [(list-rest (Tuple cursor goals) _) 
     (let* ((goal (list-ref goals cursor))
            (formals (Goal-formals goal))
            (domains (Goal-doms goal))
            (formals-ct (length formals)))
       (display "[forall] ")
       (for ((formal formals)
             (domain domains)
             (index (range formals-ct)))
         (printf "~a : ~a" formal domain)
         (unless (equal? index (- formals-ct 1))
           (display ", ")))
       (newline)
       (displayln "[to prove]")
       (pretty-display (Goal-concl goal))
       (displayln "[assuming]")
       (for ((prem (Goal-prems goal)))
         (pretty-display prem))
       (for ((fa-prem (Goal--fa-prems goal)))
         (pretty-display fa-prem))
       (printf "[schemes used] ~a~n" (Goal-schemes goal)))]))
