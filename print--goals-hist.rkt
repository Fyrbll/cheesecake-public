#lang racket/base

(require
 cheesecake/structs
 "./env.rkt")
(provide
 (all-defined-out))

(define (repl--print--goals-hist)
  (displayln (Env--goals-hist env)))
