#lang racket/base

(require (only-in racket/syntax format-symbol))
(provide next! fresh! reset!)

(define (reset!) (hash-clear! sym->count))

(define sym->count
  (make-hash))


(define (next! sym)
  (begin0
      (hash-ref! sym->count sym 0)
    (hash-update! sym->count sym (lambda (x)
                                   (+ 1 x)))))

(define (fresh! sym)
  (format-symbol "~a~a" sym (next! sym)))
