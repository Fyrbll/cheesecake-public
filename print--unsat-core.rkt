#lang racket/base

(require
 (only-in "./env.rkt" last--unsat-core))
(provide
 (all-defined-out))


(define (print--unsat-core)
  (displayln "[last--unsat-core]")
  (for ((prem (unbox last--unsat-core)))
    (displayln prem)))
