#lang racket/base

(require
 cheesecake/structs
 cheesecake/list
 "./env.rkt")
(provide
 (all-defined-out))


(define (repl-print-tips)
  (let ((recfuns (Env-recfuns env)))
    (for ((recfun recfuns))
      (displayln (RecFun-id recfun))
      (for ((tip (RecFun-tips recfun)))
        (for ((form (append
                     (intersperse (Tip-tests tip) 'and)
                     (list '=>)
                     (intersperse (Tip-actuals* tip) '|,|))))
          (display form)
          (display " "))
        (newline))
      (newline))))


(define (repl-print-indn)
  (let ((recfuns (Env-recfuns env)))
    (for ((recfun recfuns))
      (displayln (RecFun-id recfun))
      (for ((tip (RecFun-indn recfun)))
        (for ((form (append
                     (intersperse (Tip-tests tip) 'and)
                     (list '=>)
                     (intersperse (Tip-actuals* tip) '|,|))))
          (display form)
          (display " "))
        (newline))
      (newline))))
