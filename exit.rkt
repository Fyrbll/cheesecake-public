#lang racket/base

(require
 "./env.rkt"
 (prefix-in counter: "counter.rkt")
 cheesecake/structs
 racket/match
 racket/function)
(provide
 (all-defined-out))


(define (repl-reset)
  (counter:reset!)
  (set-Env-funs! env null)
  (set-Env-recfuns! env null)
  (set-Env--goals-hist! env null)
  (let ((proc (Env-proc env)))
    (when proc
      (let ((in (Process-in proc))
            (out (Process-out proc))
            (err (Process-err proc)))
        (display '(exit) in)
        (newline in)
        (flush-output in)
        (unless (port-closed? in)
          (close-output-port in))
        (unless (port-closed? out)
          (close-input-port out))
        (unless (port-closed? err)
          (close-input-port err))
        ((Process--sig-snd proc) 'wait))))
  (set-Env-proc! env #f)
  #f)
