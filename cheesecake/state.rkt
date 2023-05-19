#lang racket/base

(require
 (only-in racket/match match-lambda match-let)
 (for-syntax (only-in racket/base lambda syntax-case syntax)))

(define (state-pure value)
  (lambda (state)
    (cons state value)))

(define (state-bind action value->action^)
  (lambda (state)
    (match-let (((cons state^ value) (action state)))
      ((value->action^ value) state^))))

(define (state-get)
  (lambda (state)
    (cons state state)))

(define (state-put state^)
  (lambda (state)
    (cons state^ null)))

(define (state-eval state action)
  (cdr (action state)))

(define (state-exec state action)
  (car (action state)))

(define-syntax state-match-let*
  (lambda (stx)
    (syntax-case stx ()
      ((_
        ((pattern action))
        result)
       (syntax
        (state-bind action (match-lambda
                             (pattern
                              result)))))
      ((_
        ((pattern action)
         (patterns actions)
         ...)
        result)
       (syntax
        (state-bind action (match-lambda
                             (pattern
                              (state-match-let*
                               ((patterns actions)
                                ...)
                               result)))))))))

(module+ main
  (state-eval
   17
   (state-match-let*
    ((counter (state-get))
     (_ (state-put (+ counter 1))))
    (state-pure 42))))
