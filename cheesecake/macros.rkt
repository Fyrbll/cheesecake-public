#lang racket/base

(require
 (only-in racket/match define-match-expander)
 (for-syntax (only-in racket/base lambda syntax syntax-case)))
(provide :: Tuple Triple Call Call* ITE ITE-make Call-args Call-fun)

(define-for-syntax ::-match-transformer
  (lambda (::-stx)
    (syntax-case ::-stx ()
      ((_ car-stx cdr-stx)
       (syntax (cons car-stx cdr-stx))))))

(define-for-syntax Tuple-match-transformer
  ::-match-transformer)

(define-for-syntax Triple-match-transformer
  (lambda (Triple-stx)
    (syntax-case Triple-stx ()
      ((_ car-stx cadr-stx cddr-stx)
       (syntax (cons car-stx (cons cadr-stx cddr-stx)))))))

(define-for-syntax Call-match-transformer
  (lambda (Call-stx)
    (syntax-case Call-stx ()
      ((_ function arguments)
       (syntax
        (cons (and function (? (lambda (x) (not (equal? 'ite x)))))
              arguments))))))

(define-for-syntax Call*-match-transformer
  (lambda (Call*-stx)
    (syntax-case Call*-stx ()
      ((_ fun args ...)
       (syntax (list fun args ...))))))

(define-for-syntax ITE-match-transformer
  (lambda (ITE-stx)
    (syntax-case ITE-stx ()
      ((_ test-stx then-stx else-stx)
       (syntax (list 'ite test-stx then-stx else-stx))))))

(define-for-syntax ::-expression-transformer
  (lambda (::-stx)
    (syntax-case ::-stx ()
      ((_ car-stx cdr-stx)
       (syntax (cons car-stx cdr-stx)))
      (_
       (syntax cons)))))

(define-for-syntax Tuple-expression-transformer
  ::-expression-transformer)

(define-for-syntax Triple-expression-transformer
  (lambda (Triple-stx)
    (syntax-case Triple-stx ()
      ((_ car-stx cadr-stx cddr-stx)
       (syntax (cons car-stx (cons cadr-stx cddr-stx))))
      (_
       (syntax Triple-make)))))

(define-for-syntax Call-expression-transformer
  ::-expression-transformer)

(define-for-syntax Call*-expression-transformer
  (lambda (Call*-stx)
    (syntax-case Call*-stx ()
      ((_ fun-stx arg-stxs ...)
       (syntax (list fun-stx arg-stxs ...)))
      (_
       (syntax list)))))

(define-for-syntax ITE-expression-transformer
  (lambda (ITE-stx)
    (syntax-case ITE-stx ()
      ((_ test-stx then-stx else-stx)
       (syntax (ITE-make test-stx then-stx else-stx))))))

(define-match-expander ::
  ::-match-transformer
  ::-expression-transformer)

(define-match-expander Tuple
  Tuple-match-transformer
  Tuple-expression-transformer)

(define-match-expander Triple
  Triple-match-transformer
  Triple-expression-transformer)

(define-match-expander Call
  Call-match-transformer
  Call-expression-transformer)

(define-match-expander Call*
  Call*-match-transformer
  Call*-expression-transformer)

(define-match-expander ITE
  ITE-match-transformer
  ITE-expression-transformer)

(define (ITE-make test-expr then-expr else-expr)
  (case test-expr
    ('true
     then-expr)
    ('false
     else-expr)
    (else
     (list 'ite test-expr then-expr else-expr))))

(define (Triple-make x y z)
  (cons x (cons y z)))

(define Call-args
  cdr)

(define Call-fun
  car)
