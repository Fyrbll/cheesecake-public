#lang racket/base

(require
 (only-in racket/match match match-lambda** match-let)
 (only-in racket/function conjoin negate))

#|
Assuming VAR? returns #t if and only if its argument is a variable symbol in
the current context, expr-occurs? returns #t if and only if the variable symbol
VAR occurs in EXPR.
|#
(define (var-occurs? var expr var?)
  (or (and (pair? expr)
           (ormap (lambda (expr^)
                    (var-occurs? var expr^ var?))
                  (cdr expr)))
      (and (symbol? expr)
           (var? expr)
           (equal? expr var))))

#|
Assuming VAR? returns #t if and only if its argument is variable symbol in the
current context, expr-unify returns a substitution that unifies EXPR0 with
EXPR1.
|#
(define (expr-unify expr0 expr1 var?)
  (let ((const? (conjoin symbol? (negate var?))))
    (cond
      ((and (const? expr0) (const? expr1) (equal? expr0 expr1))
       (list))
      ((and (const? expr0) (const? expr1))
       #f)
      ((and (var? expr0) (var? expr1) (equal? expr0 expr1))
       (list))
      ((and (var? expr0) (var? expr1))
       (list (cons expr0 expr1)))
      ((and (var? expr0) (var-occurs? expr0 expr1 var?))
       #f)
      ((var? expr0)
       (list (cons expr0 expr1)))
      ((var? expr1)
       (expr-unify expr1 expr0 var?))
      ((and (pair? expr0) (pair? expr1))
       (match-let
           (((cons expr0-fun expr0-args) expr0)
            ((cons expr1-fun expr1-args) expr1))
         (let ((expr0-args-ct (length expr0))
               (expr1-args-ct (length expr1)))
           (and (equal? expr0-fun expr1-fun)
                (equal? expr0-args-ct expr1-args-ct)
                (foldl
                 (lambda (expr0^ expr1^ substn)
                   (and substn
                        (let ((substn^ (expr-unify expr0^ expr1^ var?)))
                          (and substn^ (substn-compose substn^ substn)))))
                 null expr0-args expr1-args))))))))

#|
We know what this does. We'll delete it later.
|#
(define (expr-subst expr substn)
  (cond
    ((symbol? expr)
     (match (assoc expr substn)
       ((cons _ expr^) expr^)
       (#f expr)))
    ((pair? expr)
     (cons (car expr) (map (lambda (expr^)
                             (expr-subst expr^ substn))
                           (cdr expr))))))

(define (substn-compose substn0 substn1)
  (foldl
   (match-lambda**
    (((and entry (cons var expr)) substn0^)
     (if (assoc var substn1) substn0^ (cons entry substn0^))))
   (foldl
    (match-lambda**
     (((and entry (cons var expr)) substn1^)
      (cons (cons var (expr-subst expr substn0)) substn1^)))
    null substn1)
   substn0))

(define (example)
  (expr-unify '(car (cons x y)) '(car (cons c1 c2)) (lambda (sym) (member sym '(x y)))))

(module+ main
  (example))
