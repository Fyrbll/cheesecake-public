#lang racket/base

(require
 (rename-in
  (only-in racket/string string-join string-split)
  (string-join join) (string-split split)))
(require
 (rename-in
  (only-in racket/list range append-map list-update)
  (list-update update)))
(require 
 (rename-in 
  (only-in
   racket/pretty pretty-format
   pretty-print-current-style-table
   pretty-print-extend-style-table)
  (pretty-print-current-style-table current-style-table)
  (pretty-print-extend-style-table extend-style-table)))
(require (only-in racket/function curry curryr))
(require (only-in racket/match match))
(provide 
 (all-defined-out))

(define (rest-format exp)
  (parameterize 
      ((current-style-table 
        (extend-style-table
         (current-style-table)
         (quote (<= = >= => and or ite))
         (quote (and and and and and and and)))))
    (split (pretty-format exp 78 #:mode (quote display)) "\n")))

(define (declare-datatype-format cmd)
  (match cmd
    ((list (quote declare-datatype) name constrs)
     (let ((n (length constrs)))
       (cons
        (format "(declare-datatype ~a" name)
        (map
         (lambda (i constr)
           (cond
             ((= i 0)       (format "  (~a" constr))
             ((= i (- n 1)) (format "   ~a))" constr))
             (else          (format "   ~a" constr))))
         (range n) constrs))))))

(define (define-fun-rec-format cmd)
  (match cmd
    ((list (quote define-fun-rec) name formals rng body)
     (let* ((body-strs (rest-format body))
            (n (length body-strs)))
       (cons 
        (format "(define-fun-rec ~a ~a ~a" name formals rng)
        (map
         (lambda (i body-str)
           (cond
             ((= i (- n 1)) (format "  ~a)" body-str))
             (else          (format "  ~a" body-str))))
         (range n) body-strs))))))

(define (prove-format cmd)
  (match cmd
    ((list (quote prove) (list (quote forall) formals body))
     (let* ((body-strs (rest-format body))
            (n (length body-strs)))
       (cons
        (format "(prove (forall ~a" formals)
        (map
         (lambda (i body-str)
           (cond
             ((= i (- n 1)) (format "  ~a))" body-str))
             (else          (format "  ~a" body-str))))
         (range n) body-strs))))))

(define (assert-not-forall-format cmd)
  (match cmd
    ((list (quote assert) (list (quote not) (list (quote forall) formals body)))
     (let* ((body-strs (rest-format body))
            (n (length body-strs)))
       (cons
        (format "(assert (not (forall ~a" formals)
        (map
         (lambda (i body-str)
           (cond
             ((= i (- n 1)) (format "  ~a)))" body-str))
             (else          (format "  ~a" body-str))))
         (range n) body-strs))))))

(define (cmd-format cmd)
  (join
   (match cmd
     ((cons (quote declare-datatype) _)
      (declare-datatype-format cmd))
     ((cons (quote define-fun-rec) _)
      (define-fun-rec-format cmd))
     ((cons (quote prove) _)
      (prove-format cmd))
     ((list (quote assert) (list (quote not) (cons (quote forall) _)))
      (assert-not-forall-format cmd))
     (_ 
      (rest-format cmd)))
   "\n"))

(define statement-format cmd-format)
