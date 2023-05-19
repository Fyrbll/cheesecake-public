#lang racket/base

(require
 "./macros.rkt"
 "./structs.rkt"
 (only-in racket/function curry curryr)
 (only-in racket/list first)
 (only-in racket/match match)
 (only-in racket/set set set-add set-member?))
(provide expr-subst expr-inline expr-desugar expr-has-var? expr-calls
         expr-normalize expr-has-ite? exprs--var-set expr-const? call-args
         expr-var? (struct-out Rule) (struct-out Tip) exprs-or exprs-and
         expr-negate exprs-calls)

(struct Rule (name formals body) #:transparent)

#|
apply `substn` to `expression`
|#
(define (expr-subst expr substn)
  (let ((recur (curryr expr-subst substn)))
    (match expr
      ((? integer?)
       expr)
      ((? symbol?)
       (match (assoc expr substn)
         ((Tuple _ expr^) expr^)
         (#f expr)))
      ((ITE test-expr then-expr else-expr)
       (ITE (recur test-expr) (recur then-expr) (recur else-expr)))
      ((Call func exprs)
       (Call func (map recur exprs))))))

#|
`rules` is a list of `(Rule name formals body)` structs, and whenever
`(function . arguments)` occurs in `expression` and `function` equals
`name` (both are symbols), then it is replaced with
`body`[`exprs`/`formals`]
|#
(define (expr-inline expr funs)
  (let ((recur (curryr expr-inline funs)))
    (match expr
      ((? integer?)
       expr)
      ((? symbol?)
       expr)
      ((ITE test-expr then-expr else-expr)
       (ITE (recur test-expr) (recur then-expr) (recur else-expr)))
      ((Call function exprs)
       (let ((exprs^ (map recur exprs)))
         (match (findf (compose (curry equal? function) Fun-id) funs)
           ((Fun _ formals _ _ body)
            (let ((substn (map Tuple formals exprs^)))
              (expr-subst body substn)))
           (#f (Call function exprs^))))))))

#|
perform the rewrites
`(and)` to `true`
`(and x)` to `x`
`(and x y)` to `(ite x y false)`
`(or)` to `false`
`(or x)` to `x`
`(or x y)` to `(ite x true y)`
`(=> x y)` to `(ite x y true)`
and for any `ite` created this way
`(ite true y z)` is `y`
`(ite false y z)` is `z`
|#
(define (expr-desugar expr)
  (match expr
    ((? integer?)
     expr)
    ((? symbol?)
     expr)
    ((ITE test-expr then-expr else-expr)
     (ITE (expr-desugar test-expr)
          (expr-desugar then-expr)
          (expr-desugar else-expr)))
    ((Call func exprs)
     (let ((exprs^ (map expr-desugar exprs)))
       (case func
         ('and
          (and-desugar exprs^))
         ('or
          (or-desugar exprs^))
         ('=>
          (implies-desugar exprs^))
         (else
          (Call func exprs^)))))))

(define (and-desugar exprs)
  (match exprs
    ((list)
     'true)
    ((list expr)
     expr)
    ((:: expr exprs)
     (ITE expr (and-desugar exprs) 'false))))

(define (or-desugar exprs)
  (match exprs
    ((list)
     'false)
    ((list expr)
     expr)
    ((:: expr exprs)
     (ITE expr 'true (or-desugar exprs)))))

(define (implies-desugar exprs)
  (match exprs
    ((list left-expr right-expr)
     (ITE left-expr right-expr 'true))
    ((:: expr exprs)
     (ITE expr (implies-desugar exprs) 'true))))

#|
returns the set of calls to all functions in `expression` whose names are
listed in `names`
|#
(define (exprs-calls exprs names (acc (set)))
  (match exprs
    ((list)
     acc)
    ((:: expr rest-exprs)
     (match expr
       ((? integer?)
        (exprs-calls rest-exprs names acc))
       ((? symbol?)
        (exprs-calls rest-exprs names acc))
       ((ITE test-expr then-expr else-expr)
        (exprs-calls
         (:: test-expr (:: then-expr (:: else-expr rest-exprs))) names acc))
       ((Call func call-exprs)
        (let ((acc^ (if (member func names) (set-add acc expr) acc)))
          (exprs-calls (append call-exprs rest-exprs) names acc^)))))))

(define (expr-calls expr names)
  (exprs-calls (list expr) names (set)))

#|
returns `#t` if `expression` mentions `variable`, else `#f`
|#
(define (exprs-have-var? exprs var)
  (match exprs
    ((list) #f)
    ((:: expr rest-exprs)
     (match expr
       ((? integer?)
        (exprs-have-var? rest-exprs var))
       ((? symbol?)
        (or (equal? expr var) (exprs-have-var? rest-exprs var)))
       ((ITE test-expr then-expr else-expr)
        (exprs-have-var?
         (:: test-expr (:: then-expr (:: else-expr rest-exprs))) var))
       ((Call func call-exprs)
        (exprs-have-var? (append call-exprs rest-exprs) var))))))

(define (expr-has-var? expr var)
  (exprs-have-var? (list expr) var))

#|
returns `#t` if `expr` ever calls `ite`
|#
(define (expr-has-ite? expr)
  (exprs-have-ite? (list expr)))

(define (exprs-have-ite? exprs)
  (match exprs
    ((list) #f)
    ((:: expr rest-exprs)
     (match expr
       ((? integer?)
        (exprs-have-ite? rest-exprs))
       ((? symbol?)
        (exprs-have-ite? rest-exprs))
       ((ITE test-expr then-expr else-expr)
        #t)
       ((Call func call-exprs)
        (exprs-have-ite? (append call-exprs rest-exprs)))))))

#|
transforms an expression into an equivalent expression that matches the grammar
TODO
|#
(define (expr-normalize expr (then-normalize? #t) (else-normalize? #t))
  (match expr
    ((? integer?)
     expr)
    ((? symbol?)
     expr)
    ((ITE test-expr
          then-expr
          else-expr)
     (let ((then-expr^ (if then-normalize?
                           (expr-normalize then-expr #t #t)
                           then-expr))
           (else-expr^ (if else-normalize?
                           (expr-normalize else-expr #t #t)
                           else-expr)))
       (match test-expr
         ((? integer?)
          (ITE test-expr
               then-expr^
               else-expr^))
         ((? symbol?)
          (ITE test-expr
               then-expr^
               else-expr^))
         ((ITE inner-test-expr
               inner-then-expr
               inner-else-expr)
          (expr-normalize
           (ITE inner-test-expr
                (expr-normalize
                 (ITE inner-then-expr
                      then-expr^
                      else-expr^)
                 #f #f)
                (expr-normalize
                 (ITE inner-else-expr
                      then-expr^
                      else-expr^)
                 #f #f))
           #f #f))
         ((Call func exprs)
          (if (expr-has-ite? test-expr)
              (expr-normalize
               (ITE (Call-normalize
                     func (map (curryr expr-normalize #t #t) exprs) null)
                    then-expr^
                    else-expr^))
              (ITE test-expr
                   then-expr^
                   else-expr^))))))
    ((Call func exprs)
     (Call-normalize func (map (curryr expr-normalize #t #t) exprs) null))))

(define (Call-normalize func exprs acc)
  (match exprs
    ((list)
     (Call func (reverse acc)))
    ((:: expr rest-exprs)
     (match expr
       ((? integer?)
        (Call-normalize func rest-exprs (:: expr acc)))
       ((? symbol?)
        (Call-normalize func rest-exprs (:: expr acc)))
       ((ITE test-expr then-expr else-expr)
        (ITE test-expr
             (Call-normalize func (:: then-expr rest-exprs) acc)
             (Call-normalize func (:: else-expr rest-exprs) acc)))
       ((Call call-func call-exprs)
        (Call-normalize func rest-exprs (:: expr acc)))))))


(define (exprs--var-set exprs acc)
  (match exprs
    ((list)
     acc)
    ((:: (? integer?) rest-exprs)
     (exprs--var-set rest-exprs acc))
    ((:: (? expr-const?) rest-exprs)
     (exprs--var-set rest-exprs acc))
    ((:: (and expr (? symbol?)) rest-exprs)
     (exprs--var-set rest-exprs (set-add acc expr)))
    ((:: (ITE test-expr then-expr else-expr) rest-exprs)
     (let ((new--rest-exprs (:: test-expr
                                (:: then-expr
                                    (:: else-expr
                                        rest-exprs)))))
       (exprs--var-set new--rest-exprs acc)))
    ((:: (Call function arguments) rest-exprs)
     (exprs--var-set (append arguments rest-exprs) acc))))


(define expr-const?
  (curry set-member? (set 'true 'false 'nil)))


(define (expr-var? expr)
  (and (symbol? expr) (not (expr-const? expr))))


(define call-args
  cdr)


(define (expr-negate expr)
  (match expr
    ((Call* 'not expr^)
     expr^)
    (_
     (Call* 'not expr))))


(define (exprs-or exprs)
  (match (length exprs)
    (0 'false)
    (1 (first exprs))
    (_ (Call 'or exprs))))


(define (exprs-and exprs)
  (match (length exprs)
    (0 'true)
    (1 (first exprs))
    (_ (Call 'and exprs))))
