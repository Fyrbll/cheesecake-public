#lang racket/base

(require
 (only-in racket/system process)
 (only-in racket/match match-let))

(define (display-newline-flush datum out)
  (display datum out)
  (newline out)
  (flush-output out))

(define (interact)
  (match-let (((list z3-out z3-in z3-pid z3-err z3-signal)
               (process "z3 -in" #:set-pwd? #t)))
    (letrec ((interact-loop
              (lambda ()
                (display "> ")
                (let ((command (read)))
                  (case (car command)
                    ((declare-datatype declare-const declare-fun define-fun
                      define-fun-rec assert push pop reset reset-assertions)
                     (display command z3-in)
                     (interact-loop))
                    ((get-assertions check-sat check-sat-assuming get-model
                      get-unsat-core eval apply)
                     (display-newline-flush command z3-in)
                     (displayln (read z3-out))
                     (interact-loop))
                    ((exit)
                     (display-newline-flush command z3-in)
                     (close-output-port z3-in)
                     (close-input-port z3-out)
                     (close-input-port z3-err)
                     (z3-signal 'wait)))))))
      (display '(set-option :interactive-mode true) z3-in)
      (display '(set-option :model true) z3-in)
      (display '(set-option :unsat_core true) z3-in)
      (display '(set-option :smt.core.minimize true) z3-in)
      (interact-loop))))

(module+ main
  (interact))
