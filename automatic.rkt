#lang racket/base

(require
 (only-in racket/function thunk)
 (only-in racket/list append-map first range rest)
 (only-in racket/match match match-define)
 cheesecake/macros
 cheesecake/structs
 "elim-destrs.rkt"
 "env.rkt"
 "induction-schemes.rkt"
 "repl-prove.rkt"
 "suggest.rkt"
 "undo.rkt")
(provide
 (all-defined-out))

#|
;;            [no]                   done
;;            ____                    /\
;;           /    \                   / [yes]
;;          /    only one 'true' goal?
;;         /     /\
;;        \/     /  [no output]
;; (repl-prove)-/
;; ^          / \  [unknown]
;; |         /  \/
;; |  [sat] /   (elim-destrs)
;; |       \/     \
;; |     fail      \ [unconditional]
;; |       /\       \
;; |        \       \/
;; |  [none] \--- (suggest)
;; \                |
;;  \               | [pick first]
;;   \              V
;;    ----------- (induct FIRST)
|#


(define (done?)
  (cond [(null? (Env--goals-hist env)) #t]
        [else
         (match-define (Tuple _ goals) (first (Env--goals-hist env)))
         (and (equal? (length goals) 1)
              (equal? (Goal-concl (first goals)) 'true))]))


(define (full-hist hist decns)
  (reverse (append hist (append-map Decn-hist decns))))


(define (automatic #:gas (gas 20))
  (let loop ([decns null] [hist null] [gas gas])
    (let/cc return
      (when (equal? gas 0)
        (return (Tuple 'out-of-gas (full-hist hist decns))))

      (when (done?)
        (return (Tuple 'success (full-hist hist decns))))

      (when (repl-prove)
        (return (loop decns (:: '(repl-prove) hist) (- gas 1))))

      (when (and (or (null? hist)
                     (not (equal? (first hist) '(elim-destrs))))
                 (expr--elim-destrs))
        (return (loop decns (:: '(elim-destrs) hist) (- gas 1))))

      (match (suggest)
        ((list)
         (when (null? decns)
           (return (Tuple 'failure (reverse hist))))
         (for ((_ hist))
           (repl-undo))
         (define decn
           (first decns))
         (set! decns (rest decns))
         (match (Decn-cont decn)
           ((list cmd)
            ((Cmd-_thunk cmd))
            (return (loop decns (:: (Cmd-symb cmd) (Decn-hist decn))
                               (- gas 1))))

           ((:: cmd cont)
            (define new-decn
              (Decn cont (Decn-hist decn)))
            ((Cmd-_thunk cmd))
            (return (loop (:: new-decn decns) (list (Cmd-symb cmd))
                               (- gas 1))))))

        ((list scheme)
         (define call
           (first (Scheme-calls scheme)))
         (induct call)
         (return (loop decns (:: `(induct ,call) hist) (- gas 1))))

        ((:: scheme schemes)
         (define cont
           (for/list ((scheme schemes)
                      #:do ((define call
                              (first (Scheme-calls scheme)))))
             (Cmd `(induct ,call) (thunk (induct call)))))
         (define decn
           (Decn cont hist))
         (define call
           (first (Scheme-calls scheme)))
         (induct call)
         (return (loop (:: decn decns) (list `(induct ,call))
                            (- gas 1))))))))
