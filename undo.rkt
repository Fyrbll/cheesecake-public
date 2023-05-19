#lang racket/base

(require
 (only-in racket/list rest)
 cheesecake/structs
 "./env.rkt")
(provide
 (all-defined-out))

(define (repl-undo)
  (update-Env--goals-hist! env rest))
