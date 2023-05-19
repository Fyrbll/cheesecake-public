#lang racket/base

(require cheesecake/structs)
(provide (all-defined-out))

(define env
  (Env null null null #f))

(define last--unsat-core
  (box null))

(define timeout
  (make-parameter 2000))
