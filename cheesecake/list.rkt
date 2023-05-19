#lang racket/base

(require
 cheesecake/macros
 (only-in racket/function curry)
 (rename-in racket/list (split-at split-at--values))
 (only-in racket/match match match-let))
(provide
 (all-defined-out))


(define (doubleton x y)
  (list x y))


(define (intersperse lst elt (acc (list)))
  (match lst
    ((list)
     (list))
    ((list elt^)
     (reverse (:: elt^ acc)))
    ((:: elt^ lst)
     (intersperse lst elt (:: elt (:: elt^ acc))))))


(define transpose
  (curry apply (curry map list)))


(define (split-at lst pos)
  (let-values
      (((x y) (split-at--values lst pos)))
    (Tuple x y)))


(define (list-remove lst pos)
  (match-let
      (((Tuple prefix (:: _ suffix)) (split-at lst pos)))
    (append prefix suffix)))


(define (>1-distinct? lst)
  (> (length (remove-duplicates lst)) 1))


(define (1-distinct? lst)
  (= (length (remove-duplicates lst)) 1))
