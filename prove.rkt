#lang racket/base

(require
 (only-in racket/list make-list cartesian-product)
 (only-in racket/match match match-let match-lambda define-match-expander
          match-let*)
 (only-in racket/pretty pretty-format pretty-print-extend-style-table
          pretty-print-current-style-table pretty-print pretty-print-columns)
 (only-in racket/set mutable-set set set-add set-add! set-remove set-member?
          set->list set-empty? set-clear! for/set set-subtract list->set
          set-intersect)
 (only-in racket/dict dict-has-key? dict-ref)
 (only-in racket/syntax format-symbol)
 (only-in racket/system system)
 (only-in racket/port port->list with-input-from-string with-output-to-string)
 (only-in racket/string string-join)
 (only-in racket/function thunk))
(require
 (for-syntax
  racket/base))
(provide
 prove)

;; PATTERNS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-match-expander ITE
  (lambda (stx)
    (syntax-case stx ()
      ((_ stx_1 stx_2 stx_3)
       #'(list (quote ite) stx_1 stx_2 stx_3)))))

(define-match-expander Apply
  (lambda (stx)
    (syntax-case stx ()
      ((_ stx_1 stx_2)
       #'(cons (and (? (lambda (x)
                         (not (equal? 'ite x))))
                    stx_1)
               stx_2)))))

;; STRUCTS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(struct Arrow (domains range) #:transparent)

;; STATE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define environment (make-hash))
(define universal null)
(define counts (make-hash))

(define definitions null)
(define constants null)
(define constants_2 null)
(define originals (make-hash))
(define explanations (make-hash))
(define instances (make-hash))
(define constraints (make-hash))
(define count_initial 0)
(define goal null)

(define ground (mutable-set))
(define interpreted (mutable-set))
(define guarded null)

(define (initialize)
  (hash-clear! environment)
  (hash-set*! environment
              'not (Arrow '(Bool) 'Bool)
              'is-nil (Arrow '(Value) 'Bool)
              '>= (Arrow '(Int Int) 'Bool)
              '< (Arrow '(Int Int) 'Bool)
              '+ (Arrow '(Int Int) 'Int)
              'cons (Arrow '(Value Value) 'Value)
              'cdr (Arrow '(Value) 'Value)
              'car (Arrow '(Value) 'Value)
              'nil 'Value
              'is-cons (Arrow '(Value) 'Bool))
  (set! universal
        (list
         '(forall ((v Value))
            (=> (is-cons v)
                (and (>= (size (car v)) 0)
                     (>= (size (cdr v)) 0))))))
  (hash-clear! counts)

  (set! definitions null)
  (set! constants null)
  (set! constants_2 null)
  (hash-clear! originals)
  (hash-clear! explanations)
  (hash-clear! instances)
  (hash-clear! constraints)
  (set! count_initial 0)
  (set! goal null)

  (set-clear! ground)
  (set-clear! interpreted)
  (set! guarded null))

(define-syntax push!
  (lambda (s)
    (syntax-case s ()
      ((_ lst elt)
       (syntax (set! lst (cons elt lst)))))))

(define-syntax queue!
  (lambda (s)
    (syntax-case s ()
      ((_ lst elt)
       (syntax (set! lst (append lst (list elt))))))))

(define-syntax dequeue!
  (lambda (s)
    (syntax-case s ()
      ((_ lst)
       (syntax
        (let ((elt (car lst)))
          (set! lst (cdr lst))
          elt))))))

(define (fresh! x)
  (let ((count_x (hash-ref counts x 0)))
    (hash-set! counts x (+ count_x 1))
    (format-symbol "~a~a" x count_x)))

(define (originals-add! body)
  (let ((name (fresh! 'original)))
    (hash-set! originals name body)))

(define (explanations-add! body)
  (let ((name (fresh! 'explanation)))
    (hash-set! explanations name body)))

(define (instances-add! body)
  (let ((name (fresh! 'instance)))
    (hash-set! instances name body)))

(define (constraints-add! body)
  (let ((name (fresh! 'constraint)))
    (hash-set! constraints name body)))

(define (update-environment)
  (for ((constant constants))
    (match constant
      ((cons name sort)
       (hash-set! environment name sort))))
  (for ((definition definitions))
    (match definition
      (`(define-fun-rec ,name ,(list `(,_ ,domains) ...) ,range
          ,_)
       (hash-set! environment name (Arrow domains range))))))

;; GROUND TERMS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (get-ground es (acc (set)))
  (match es
    ((list)
     (void))
    ((cons (? integer?) es)
     (get-ground es acc))
    ((cons (and e (? symbol?)) es)
     (let ((sort_e (dict-ref environment e #f)))
       (if (and sort_e (equal? sort_e 'Value))
           (begin
             (set-add! acc e)
             (get-ground es acc))
           (get-ground es acc))))
    ((cons (ITE e_1 e_2 e_3) es)
     (get-ground (cons e_1 (cons e_2 (cons e_3 es))) acc))
    ((cons (and e (Apply f es_2)) es_1)
     (let ((sort_f (dict-ref environment f #f)))
       (if (and sort_f (equal? (Arrow-range sort_f) 'Value))
           (begin
             (set-add! acc e)
             (get-ground (append es_2 es_1) acc))
           (get-ground (append es_2 es_1) acc))))))

;; UNINTERPRETED ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (lookup_definitions definitions name_1)
  (match definitions
    ((list)
     #f)
    ((cons (and d (list 'define-fun-rec name_2 _ _ _)) ds)
     (if (equal? name_2 name_1)
         d
         (lookup_definitions ds name_1)))))

(define (get-uninterpreted es (acc (set)))
  (match es
    ((list)
     acc)
    ((cons (? integer?) es)
     (get-uninterpreted es acc))
    ((cons (? symbol?) es)
     (get-uninterpreted es acc))
    ((cons (ITE e_1 e_2 e_3) es)
     (get-uninterpreted (cons e_1 (cons e_2 (cons e_3 es))) acc))
    ((cons (and e (Apply f es_2)) es_1)
     (if (and (lookup_definitions definitions f)
              (not (set-member? interpreted e)))
         (get-uninterpreted (append es_2 es_1) (set-add acc e))
         (get-uninterpreted (append es_2 es_1) acc)))))

;; EXPLAIN ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (substitute sigma e)
  (let ((recur (lambda (e)
                 (substitute sigma e))))
    (match e
      ((? integer?)
       e)
      ((? symbol?)
       (dict-ref sigma e e))
      ((ITE e_1 e_2 e_3)
       (cons 'ite (map recur (list e_1 e_2 e_3))))
      ((Apply f es)
       (cons f (map recur es))))))

(define (negate e)
  (match e
    ((? integer?)
     e)
    ((? symbol?)
     (list 'not e))
    ((Apply 'not (list e_1))
     e_1)
    ((Apply f es)
     (list 'not (cons f es)))
    ((ITE e_1 e_2 e_3)
     (list 'ite e_1 (negate e_2) (negate e_3)))))

(define (explain_expression type e b)
  (match e
    ((? integer?)
     e)
    ((? symbol?)
     e)
    ((Apply f es)
     e)
    ((ITE e_1 e_2 e_3)
     #:when (pair? (get-uninterpreted (list e_1)))
     e)
    ((ITE e_1 e_2 e_3)
     (let* ((t (fresh! 't))
            (b_1 (fresh! 'b))
            (b_2 (fresh! 'b))
            (|e_2'| (explain_expression type e_2 b_1))
            (|e_3'| (explain_expression type e_3 b_2)))
       (hash-set! environment t type)
       (hash-set! environment b_1 'Bool)
       (hash-set! environment b_2 'Bool)
       (push! constants_2 (cons t type))
       (push! constants_2 (cons b_1 'Bool))
       (push! constants_2 (cons b_2 'Bool))
       (explanations-add! (list '= b_1 (list 'and b e_1)))
       (explanations-add! (list '= b_2 (list 'and b (negate e_1))))
       (explanations-add! (list '=> b_1 (list '= t |e_2'|)))
       (explanations-add! (list '=> b_2 (list '= t |e_3'|)))
       (get-ground (list e_1) ground)
       (get-ground (list |e_2'|) ground)
       (get-ground (list |e_3'|) ground)
       (let* ((u (get-uninterpreted (list |e_2'|))))
         (when (not (set-empty? u))
           (queue! guarded (cons b_1 (set->list u)))))
       (let* ((u (get-uninterpreted (list |e_3'|))))
         (when (not (set-empty? u))
           (queue! guarded (cons b_2 (set->list u)))))
       t))))

(define (explain e)
  (match-let (((Apply f actuals) e))
    (match (lookup_definitions definitions f)
      (`(define-fun-rec ,name ((,formals ,_) ...) ,range
          ,body)
       (let* ((sigma (map cons formals actuals))
              (|e'| (explain_expression range (substitute sigma body) 'true)))
         (explanations-add! (list '= e |e'|))))
      (_
       (void)))))

;; INSTANTIATE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; NOTE: Can I fix 'instantiate' to work with universally quantified hyps
;; whose variables aren't of sort 'Value' ?
(define (instantiate)
  (hash-clear! instances)
  (hash-set! counts 'instance 0)

  (for ((u universal))
    (match-let*
        ((`(forall ,(list `(,formals ,_) ...)
             ,body) u)
         (actuals* (apply cartesian-product
                          (make-list (length formals)
                                     (set->list ground)))))
      (for ((actuals actuals*))
        (instances-add!
         (substitute (map cons formals actuals) body))))))

;; DEQUEUE ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (guarded-dequeue)
  (letrec
      ((loop (lambda (uninterpreted-calls stop?)
               (match uninterpreted-calls
                 ((list)
                  stop?)
                 ((cons uninterpreted-call uninterpreted-calls)
                  (if (set-member? interpreted uninterpreted-call)
                      (loop uninterpreted-calls stop?)
                      (begin
                        ;;(printf "[explaining] ~a~n" uninterpreted-call)
                        (explain uninterpreted-call)
                        (set-add! interpreted uninterpreted-call)
                        (loop uninterpreted-calls #t))))))))
    (when (pair? guarded)
      (match-let*
          (((cons _ uninterpreted-calls) (dequeue! guarded))
           (stop? (loop uninterpreted-calls #f)))
        (if stop?
            (instantiate)
            (guarded-dequeue))))))

;; PRINT ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (format-type t)
  (match t
    ((? symbol?)
     (symbol->string t))
    ((Arrow domains range)
     (format "~a -> ~a" domains range))))

(define (state-print)
  (hash-for-each environment
    (lambda (v t)
      (printf "~a : ~a~n" v (format-type t))))
  (newline)
  (displayln "Initial Hypotheses:")
  (hash-for-each originals
    (lambda (name body)
      (printf "~a [~a]~n" body name)))
  (newline)
  (displayln "Extra Hypotheses:")
  (hash-for-each explanations
    (lambda (name body)
      (printf "~a [~a]~n" body name)))
  (newline)
  (printf "Instances: ~a~n" (hash-count instances))
  (newline)
  (displayln "Goal:")
  (displayln goal)
  (newline)
  (displayln "Ground Terms:")
  (parameterize ((pretty-print-columns 80))
    (pretty-print ground))
  (newline)
  (displayln "Interpreted Calls:")
  (parameterize ((pretty-print-columns 80))
    (pretty-print interpreted))
  (newline)
  (displayln "Uninterpreted Calls:")
  (for ((g guarded))
    (displayln g)))

;; LOOP ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (decide gas)
  (when (> gas 0)
    (guarded-dequeue)

    (match (state-query #t)
      ((and response (cons 'sat model))
       response)
      ((cons 'unsat core)
       (match (state-query #f)
         ((and response (cons 'unsat core))
          #;(for ((name core))
              (displayln
               (cond
                 ((hash-has-key? originals name)
                  (hash-ref originals name))
                 ((hash-has-key? explanations name)
                  (hash-ref explanations name))
                 ((hash-has-key? instances name)
                  (hash-ref instances name))
                 ((hash-has-key? constraints name)
                  (hash-ref constraints name)))))
          response)
         ((cons 'sat model)
          (decide (- gas 1))))))))

;; IMPORTANT. Solely over-constraining might fail when both branches of one
;; 'ite' contain recursive calls and get 'disabled,' while the original lemmas
;; prevent you from hitting the base case, and you always get an 'unsat' that
;; relies on the constraint lemmas, and your prover spins out without doing any
;; meaningful work
;; IDEA. It's not a new chain with each unfolding! Can we use the old 'guard'
;; literal as a 'base' for the next unfolding of the functions that it guards,
;; instead of using 'true' ?
#;(define (decide gas)
  (if (<= gas 0)
      (error "decide: timeout")
      (begin
        (guarded-dequeue)

        (match (state-query #t)
          ((and response (cons 'sat model))
           response)
          ((and response (cons 'unsat core))
           (displayln "[core]")
           (for ((name core))
             (displayln
              (cond
                ((hash-has-key? originals name)
                 (hash-ref originals name))
                ((hash-has-key? explanations name)
                 (hash-ref explanations name))
                ((hash-has-key? instances name)
                 (hash-ref instances name))
                ((hash-has-key? constraints name)
                 (hash-ref constraints name)))))
           (newline)
           (if (set-empty?
                (set-intersect
                 (list->set core)
                 (list->set (hash-keys constraints))))
               response
               (decide (- gas 1))))))))

(define (model-lookup model name)
  (match model
    ((list)
     #f)
    ((cons (and defn `(define-fun ,name_1 ,_ ,_
                        ,body))
           model)
     #:when (equal? name_1 name)
     defn)
    ((cons _ model)
     (model-lookup model name))))

(define (state-query constrained?)
  (let*
      ((query
        (with-output-to-string
          (thunk
           (write '(set-option :produce-unsat-cores true))
           (write '(set-option :produce-unsat-cores true))
           (write '(set-option :smt.core.minimize true))
           (write '(declare-datatype Value
                     ((err)
                      (nil)
                      (bool (unbool Bool))
                      (int (unint Int))
                      (cons (car Value) (cdr Value)))))
           (write '(declare-datatype Flag2
                     ((Flag2-0)
                      (Flag2-1))))
           (for ((definition definitions))
             (match-let
                 ((`(define-fun-rec ,name ,(list `(,_ ,domains) ...) ,range
                      ,_) definition))
               (write `(declare-fun ,name ,domains ,range))))
           (for ((constant constants))
             (match-let
                 (((cons name type) constant))
               (write `(declare-const ,name ,type))))
           (for ((constant constants_2))
             (match-let
                 (((cons name type) constant))
               (write `(declare-const ,name ,type))))
           (hash-for-each originals
             (lambda (name body)
               (write `(assert (! ,body :named ,name)))))
           (hash-for-each explanations
             (lambda (name body)
               (write `(assert (! ,body :named ,name)))))
           (hash-for-each instances
             (lambda (name body)
               (write `(assert (! ,body :named ,name)))))
           (write `(assert ,(negate goal)))
           (hash-clear! constraints)
           (hash-set! counts 'constraint 0)
           (when constrained?
             (for ((g guarded))
               (match-let (((cons ?b _) g))
                 (when ?b
                   (constraints-add! `(not ,?b))))))
           (hash-for-each constraints
             (lambda (name body)
               (write `(assert (! ,body :named ,name)))))
           (write '(check-sat))
           (write '(get-unsat-core))
           (write '(get-model)))))
       (response
        (with-input-from-string (with-output-to-string
                                  (thunk
                                   (with-input-from-string query
                                     (thunk
                                      (system "z3 -in" #:set-pwd? #t)))))
          (thunk (port->list read)))))
    (match response
      ((list 'sat _ model)
       (cons 'sat
             (foldl
              (lambda (constant acc)
                (match-let*
                    (((cons name _) constant)
                     (?definition (model-lookup model name)))
                  (if ?definition
                      (cons ?definition acc)
                      acc)))
              null constants)))
      ((list 'unsat core _)
       (cons 'unsat core))
      (other
       (error (format "state-query: ~a" other))))))

;; TESTS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (prove definitions_in constants_in hypotheses_in goal_in
               (universal_in (list)))
  (initialize)

  (for ((lemma universal_in))
    (push! universal lemma))

  (set! definitions definitions_in)
  (for ((d definitions))
    (match-let ((`(define-fun-rec ,name ,(list `(,_ ,domains) ...) ,range
                    ,_) d))
      (hash-set! environment name (Arrow domains range))))

  (set! constants constants_in)
  (for ((c constants))
    (match-let (((cons name type) c))
      (hash-set! environment name type)))

  (for ((hypothesis hypotheses_in))
    (originals-add! hypothesis))
  (get-ground hypotheses_in ground)

  (set! count_initial (length hypotheses_in))

  (set! goal goal_in)
  (get-ground hypotheses_in ground)

  (let* ((u (get-uninterpreted (cons goal_in hypotheses_in))))
    (unless (set-empty? u)
      (queue! guarded (cons #f (set->list u)))))

  (match (decide 6)
    ((cons 'sat model)
     (cons 'sat model))
    ((cons 'unsat core)
     (cons 'unsat
           (foldl (lambda (name accumulator)
                    (if (hash-has-key? originals name)
                        (cons (hash-ref originals name)
                              accumulator)
                        accumulator))
                  null core)))))

(define (test_1)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-nil v)
            0
            (ite (is-cons v)
                 (+ 1 (size (car v)) (size (cdr v)))
                 0))))
   (list
    '(v . Value))
   (list
    '(not (is-nil v))
    '(is-cons v)
    '(is-nil (car v)))
   '(< (size (cdr v)) (size v))))

(define (test_2)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-nil v)
            0
            (ite (is-cons v)
                 (+ 1 (size (car v)) (size (cdr v)))
                 0))))
   (list
    '(v . Value))
   (list
    '(not (is-nil v))
    '(is-cons v)
    '(is-nil (car v)))
   '(> (size (cdr v)) (size v))))

(define (test_3)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (= 42 42)
            (ite (is-nil v)
                 0
                 (ite (is-cons v)
                      (+ 1 (size (car v)) (size (cdr v)))
                      0))
            -1)))
   (list
    '(v . Value))
   (list
    '(not (is-nil v))
    '(is-cons v))
   '(< (size (car v)) (size v))))

(define (test_4)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-nil v)
            0
            (ite (is-cons v)
                 (+ 1 (size (car v)) (size (cdr v)))
                 0))))
   (list
    (cons 'v 'Value))
   (list
    '(not (is-nil v))
    '(is-cons v)
    '(is-nil (car v))
    '(is-cons (cdr v))
    '(is-nil (car (cdr v))))
   '(< (size (cdr (cdr v))) (size v))))

(define (test_5)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-nil v)
            0
            (ite (is-cons v)
                 (ite (is-nil (car v))
                      (+ 1 0 (size (cdr v)))
                      (ite (is-cons (car v))
                           (+ 1
                              (+ 1 (size (car (car v))) (size (cdr (car v))))
                              (size (cdr v)))
                           (+ 1 0 (size (cdr v)))))
                 0)))
    '(define-fun-rec is-nat ((v Value)) Bool
       (ite (is-nil v)
            true
            (ite (is-cons v)
                 (ite (is-nil (car v))
                      (is-nat (cdr v))
                      false)
                 false))))
   (list
    (cons 'v 'Value))
   (list
    '(not (is-nil v))
    '(is-cons v)
    '(is-cons (car v))
    '(not (is-nat (car (car v)))))
   '(< (size (cdr v)) (size v))))

(define (test_6)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-nil v)
            0
            (ite (is-cons v)
                 (+ 1 (size (car v)) (size (cdr v)))
                 0)))
    '(define-fun-rec is-nat ((v Value)) Bool
       (ite (is-nil v)
            true
            (ite (is-cons v)
                 (ite (is-nil (car v))
                      (is-nat (cdr v))
                      false)
                 false))))
   (list
    (cons 'v 'Value))
   (list
    '(not (is-nil v))
    '(is-cons v)
    '(is-cons (car v))
    '(is-nat (car (car v)))
    '(is-nat (cdr (cdr v))))
   '(< (size (cdr v)) (size v))))

(define (test_7)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-nil v)
            0
            (ite (is-cons v)
                 (+ 1 (size (car v)) (size (cdr v)))
                 0))))
   (list
    (cons 'v 'Value)
    (cons 'f 'Flag2))
   (list
    '(not (= f Flag2-0))
    '(= f Flag2-1)
    '(is-cons v)
    '(is-nil (car v)))
   '(< (size (cdr v)) (size v))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (test_8)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-err v)  0
       (ite (is-nil v)  0
       (ite (is-bool v) 0
       (ite (is-int v)  0
       (ite (is-cons v) (+ 1 (size (car v)) (size (cdr v)))
                        0)))))))
   (list
    (cons 'm 'Value)
    (cons 'n 'Value))
   (list
    '(is-int m)
    '(is-int n)
    '(not (>= (unint m) (unint n))))
   '(< (- (unint n) (unint (int (+ (unint m) 1))))
       (- (unint n) (unint m)))))

(define (test_9)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-err v)  0
       (ite (is-nil v)  0
       (ite (is-bool v) 0
       (ite (is-int v)  0
       (ite (is-cons v) (+ 1 (size (car v)) (size (cdr v)))
                        0)))))))
   (list
    (cons 'v 'Value))
   (list
    '(not (is-nil v))
    '(is-cons v))
   '(< (size (cdr v)) (size v))))

(define (test_10)
  (prove
   (list
    '(define-fun-rec listp ((v Value)) Value
       (bool (or (is-nil v)
                 (and (is-cons v)
                      (is-bool (listp (cdr v)))
                      (unbool (listp (cdr v)))))))
    '(define-fun-rec size ((v Value)) Int
       (ite (is-err v)  0
       (ite (is-nil v)  0
       (ite (is-bool v) 0
       (ite (is-int v)  0
       (ite (is-cons v) (+ 1 (size (car v)) (size (cdr v)))
                        0)))))))
   (list
    (cons 'x 'Value)
    (cons 'y 'Value))
   (list
    '(is-bool (listp y))
    '(unbool (listp y))
    '(is-int x)
    '(> (unint x) 0)
    '(is-cons y))
   '(< (unint (int (- (unint x) 1))) (unint x))))

(define (test_11)
  (prove
   (list
    '(define-fun-rec listp ((v Value)) Value
       (bool (or (is-nil v)
                 (and (is-cons v)
                      (is-bool (listp (cdr v)))
                      (unbool (listp (cdr v)))))))
    '(define-fun-rec size ((v Value)) Int
       (ite (is-err v)  0
       (ite (is-nil v)  0
       (ite (is-bool v) 0
       (ite (is-int v)  0
       (ite (is-cons v) (+ 1 (size (car v)) (size (cdr v)))
                        0)))))))
   (list
    (cons 'x 'Value)
    (cons 'y 'Value))
   (list
    '(is-bool (listp x))
    '(unbool (listp x))
    '(is-bool (listp y))
    '(unbool (listp y))
    '(not (is-nil x))
    '(is-cons x))
   '(< (size (cdr x)) (size x))))

;; This test is interesting because it suggests two separate inductions.
(define (test_12)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec natural ((v Value)) Bool
       (ite (is-nil v)
            true
            (ite (is-cons v)
                 (ite (is-nil (car v))
                      (natural (cdr v))
                      false)
                 false)))
    '(define-fun-rec greaterthan ((n Value) (m Value)) Bool
       (ite (is-cons n)
            (ite (is-nil m)
                 true
                 (ite (is-cons m)
                      (greaterthan (cdr n) (cdr m))
                      false))
            false))
    '(define-fun-rec monus ((n Value) (m Value)) Value
       (ite (is-nil n)
            n
            (ite (is-cons n)
                 (ite (is-nil m)
                      n
                      (ite (is-cons m)
                           (monus (cdr n) (cdr m))
                           err))
                 err))))
   (list
    (cons 'n 'Value)
    (cons 'm 'Value))
   (list
    '(natural n)
    '(natural m)
    '(greaterthan n m)
    '(=> (is-cons n)
         (is-cons m)
         (natural (cdr n))
         (natural (cdr m))
         (greaterthan (cdr n) (cdr m))
         (< (size (monus (cdr n) (cons nil (cdr m))))
            (size (monus (cdr n) (cdr m))))))
   '(< (size (monus n (cons nil m)))
       (size (monus n m)))))

(define (test_13)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec natural ((v Value)) Bool
       (ite (is-nil v)
            true
            (ite (is-cons v)
                 (ite (is-nil (car v))
                      (natural (cdr v))
                      false)
                 false)))
    '(define-fun-rec greaterthan ((n Value) (m Value)) Bool
       (ite (is-cons n)
            (ite (is-nil m)
                 true
                 (ite (is-cons m)
                      (greaterthan (cdr n) (cdr m))
                      false))
            false))
    '(define-fun-rec monus ((n Value) (m Value)) Value
       (ite (is-nil n)
            n
            (ite (is-cons n)
                 (ite (is-nil m)
                      n
                      (ite (is-cons m)
                           (monus (cdr n) (cdr m))
                           err))
                 err))))
   (list
    (cons 'n 'Value)
    (cons 'm 'Value))
   (list
    '(natural n)
    '(natural m))
   '(< (size (monus n (cons nil m)))
       (size (monus n m)))))

(define (test_13_1)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec natural ((v Value)) Bool
       (ite (is-nil v)
            true
            (ite (is-cons v)
                 (ite (is-nil (car v))
                      (natural (cdr v))
                      false)
                 false)))
    '(define-fun-rec greaterthan ((n Value) (m Value)) Bool
       (ite (is-cons n)
            (ite (is-nil m)
                 true
                 (ite (is-cons m)
                      (greaterthan (cdr n) (cdr m))
                      false))
            false))
    '(define-fun-rec monus ((n Value) (m Value)) Value
       (ite (is-nil n)
            n
            (ite (is-cons n)
                 (ite (is-nil m)
                      n
                      (ite (is-cons m)
                           (monus (cdr n) (cdr m))
                           err))
                 err))))
   (list
    (cons 'n 'Value)
    (cons 'm 'Value))
   (list
    '(natural n)
    '(natural m)
    '(greaterthan n m))
   '(< (size (monus n (cons nil m)))
       (size (monus n m)))
   (list
    '(forall ((l Value))
       (=> (is-cons n)
           (natural (cdr n))
           (natural l)
           (greaterthan (cdr n) l)
           (< (size (monus (cdr n) (cons nil l)))
              (size (monus (cdr n) l))))))))

(define (test_14)
  (prove
   (list)
   (list
    (cons 'n 'Int)
    (cons 'm 'Int))
   (list
    '(> m 0)
    '(> n 0)
    '(not (= m n))
    '(< m n))
   '(< (+ (- n m) m) (+ m n))))

(define (test_15)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec less-than ((v Value) (w Value)) Bool
       (ite (is-int v)
            (ite (is-int w)
                 (ite (< (unint v) (unint w))
                      true
                      (ite (is-cons v)
                           (ite (is-cons w)
                                (ite (is-int (car v))
                                     (ite (is-int (car w))
                                          (ite (< (unint (car v)) (unint (car w)))
                                               true
                                               (ite (=
                                                     (unint (car v))
                                                     (unint (car w)))
                                                    (less-than (cdr v) (cdr w))
                                                    false))
                                          false)
                                     false)
                                false)
                           false))
                 (ite (is-cons v)
                      (ite (is-cons w)
                           (ite (is-int (car v))
                                (ite (is-int (car w))
                                     (ite (< (unint (car v)) (unint (car w)))
                                          true
                                          (ite (= (unint (car v)) (unint (car w)))
                                               (less-than (cdr v) (cdr w))
                                               false))
                                     false)
                                false)
                           false)
                      false))
            (ite (is-cons v)
                 (ite (is-cons w)
                      (ite (is-int (car v))
                           (ite (is-int (car w))
                                (ite (< (unint (car v)) (unint (car w)))
                                     true
                                     (ite (= (unint (car v)) (unint (car w)))
                                          (less-than (cdr v) (cdr w))
                                          false))
                                false)
                           false)
                      false)
                 false))))
   (list
    (cons 'm 'Int)
    (cons 'n 'Int))
   (list
    '(not (<= m 0))
    '(<= n 0))
   '(less-than (cons (int (ite (<= m 0) 0 (- m 1))) (int 1))
               (cons (int m) (int n)))))

;; unsat, as expected
(define (test_16)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec is-natural ((x Value)) Bool
       (ite (is-nil x)
            true
            (ite (is-cons x)
                 (is-natural (cdr x))
                 false)))
    '(define-fun-rec less-or-equal ((x Value) (y Value)) Bool
       (ite (is-nil x)
            true
            (ite (is-cons x)
                 (ite (is-nil y)
                      false
                      (ite (is-cons y)
                           (less-or-equal (cdr x) (cdr y))
                           false))
                 false)))
    '(define-fun-rec minimum ((x Value) (y Value)) Value
       (ite (is-nil x)
            x
            (ite (is-cons x)
                 (ite (is-nil y)
                      y
                      (ite (is-cons y)
                           (cons nil (minimum (cdr x) (cdr y)))
                           nil))
                 nil))))
   (list
    (cons 'n 'Value)
    (cons 'm 'Value))
   (list
    '(is-natural n)
    '(is-natural m)
    '(=> (is-cons n)
         (is-cons m)
         (is-natural (cdr n))
         (is-natural (cdr m))
         (less-or-equal (minimum (cdr n) (cdr m)) (cdr n))))
   '(less-or-equal (minimum n m) n)))

;; remove (is-cons m) assertion ;; still unsat
(define (test_17)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec is-natural ((x Value)) Bool
       (ite (is-nil x)
            true
            (ite (is-cons x)
                 (is-natural (cdr x))
                 false)))
    '(define-fun-rec less-or-equal ((x Value) (y Value)) Bool
       (ite (is-nil x)
            true
            (ite (is-cons x)
                 (ite (is-nil y)
                      false
                      (ite (is-cons y)
                           (less-or-equal (cdr x) (cdr y))
                           false))
                 false)))
    '(define-fun-rec minimum ((x Value) (y Value)) Value
       (ite (is-nil x)
            x
            (ite (is-cons x)
                 (ite (is-nil y)
                      y
                      (ite (is-cons y)
                           (cons nil (minimum (cdr x) (cdr y)))
                           nil))
                 nil))))
   (list
    (cons 'n 'Value)
    (cons 'm 'Value))
   (list
    '(is-natural n)
    '(is-natural m)
    '(=> (is-cons n)
         (is-natural (cdr n))
         (is-natural (cdr m))
         (less-or-equal (minimum (cdr n) (cdr m)) (cdr n))))
   '(less-or-equal (minimum n m) n)))

;; ask to prove something wrong
;; NOTE: it's possible for counterexamples to mention 'err'
;; should this be allowed?
(define (test_18)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec is-natural ((x Value)) Bool
       (ite (is-nil x)
            true
            (ite (is-cons x)
                 (is-natural (cdr x))
                 false)))
    '(define-fun-rec more-or-equal ((x Value) (y Value)) Bool
       (ite (is-nil x)
            (is-nil y)
            (ite (is-cons x)
                 (ite (is-nil y)
                      true
                      (ite (is-cons y)
                           (more-or-equal (cdr x) (cdr y))
                           false))
                 false)))
    '(define-fun-rec minimum ((x Value) (y Value)) Value
       (ite (is-nil x)
            x
            (ite (is-cons x)
                 (ite (is-nil y)
                      y
                      (ite (is-cons y)
                           (cons nil (minimum (cdr x) (cdr y)))
                           nil))
                 nil))))
   (list
    (cons 'n 'Value)
    (cons 'm 'Value))
   (list
    '(is-natural n)
    '(is-natural m)
    '(=> (is-cons n)
         (is-natural (cdr n))
         (is-natural (cdr m))
         (more-or-equal (minimum (cdr n) (cdr m)) (cdr n))))
   '(more-or-equal (minimum n m) n)))

(define (test_19)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int
       (ite (is-cons v)
            (+ 1 (size (car v)) (size (cdr v)))
            0))
    '(define-fun-rec more-or-equal ((x Value) (y Value)) Bool
       (ite (is-nil x)
            (is-nil y)
            (ite (is-cons x)
                 (ite (is-nil y)
                      true
                      (ite (is-cons y)
                           (more-or-equal (cdr x) (cdr y))
                           false))
                 false)))
    '(define-fun-rec is-natural ((x Value)) Bool
       (ite (is-nil x)
            true
            (ite (is-cons x)
                 (is-natural (cdr x))
                 false)))
    '(define-fun-rec less-or-equal ((x Value) (y Value)) Bool
       (ite (is-nil x)
            true
            (ite (is-cons x)
                 (ite (is-nil y)
                      false
                      (ite (is-cons y)
                           (less-or-equal (cdr x) (cdr y))
                           false))
                 false)))
    '(define-fun-rec minimum ((x Value) (y Value)) Value
       (ite (is-nil x)
            x
            (ite (is-cons x)
                 (ite (is-nil y)
                      (cdr y)
                      (ite (is-cons y)
                           (cons nil (minimum (cdr x) (cdr y)))
                           nil))
                 nil))))
   (list
    (cons 'n 'Value)
    (cons 'm 'Value))
   (list
    '(is-natural n)
    '(is-natural m)
    '(is-cons n)
    '(is-cons m)
    '(=> (is-cons n)
         (is-cons m)
         (is-natural (cdr n))
         (is-natural (cdr m))
         (less-or-equal (minimum (cdr n) (cdr m)) (cdr m))))
   '(less-or-equal (minimum n m) m)))

(define (test_20)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int (ite (is-cons v) (+ 1 (size (car v)) (size (cdr v))) 0))
    '(define-fun-rec less-than ((v Value) (w Value)) Bool (ite (ite (is-int v) (ite (is-int w) (< (ite (> (unint v) 0) (unint v) 0) (ite (> (unint w) 0) (unint w) 0)) false) false) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (< (ite (> (unint (car v)) 0) (unint (car v)) 0) (ite (> (unint (car w)) 0) (unint (car w)) 0)) true (ite (= (ite (> (unint (car v)) 0) (unint (car v)) 0) (ite (> (unint (car w)) 0) (unint (car w)) 0)) (less-than (cdr v) (cdr w)) false)) false) false) false) false)))
    '(define-fun-rec ackermann-peter ((m Int) (n Int)) Int (ite (> m 0) (ite (> n 0) (ackermann-peter (- m 1) (ackermann-peter m (- n 1))) 0) 0)))
   (list
    (cons 'm 'Int)
    (cons 'n 'Int))
   (list
    '(> m 0)
    '(> n 0))
   '(and (less-than (cons (int m) (int (- n 1)))
                    (cons (int m) (int n)))
         (less-than (cons (int (- m 1)) (int (ackermann-peter m (- n 1))))
                    (cons (int m) (int n))))))

(define (test_21)
  (prove
   (list
    '(define-fun-rec size ((v Value)) Int (ite (is-cons v) (+ 1 (size (car v)) (size (cdr v))) 0))
    '(define-fun-rec less-than ((v Value) (w Value)) Bool (ite (is-int v) (ite (is-int w) (ite (> (unint v) 0) (ite (> (unint w) 0) (ite (< (unint v) (unint w)) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)) (ite (< (unint v) 0) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false))) (ite (> (unint w) 0) (ite (< 0 (unint w)) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)) (ite (< 0 0) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)))) (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)) (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)))
    '(define-fun-rec ackermann-peter ((m Int) (n Int)) Int (ite (> m 0) (ite (> n 0) (ackermann-peter (- m 1) (ackermann-peter m (- n 1))) 0) 0)))
   (list
    (cons 'm 'Int)
    (cons 'n 'Int))
   (list
    '(not (<= m 0))
    '(not (<= n 0)))
   '(and (less-than (cons (int m) (int (- n 1)))
                    (cons (int m) (int n)))
         (less-than (cons (int (- m 1)) (int (ackermann-peter m (- n 1))))
                    (cons (int m) (int n))))))

(define (test_22)
  (prove
   '((define-fun-rec size ((v Value)) Int (ite (is-cons v) (+ 1 (size (car v)) (size (cdr v))) 0))
     (define-fun-rec less-than ((v Value) (w Value)) Bool (ite (is-int v) (ite (is-int w) (ite (> (unint v) 0) (ite (> (unint w) 0) (ite (< (unint v) (unint w)) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)) (ite (< (unint v) 0) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false))) (ite (> (unint w) 0) (ite (< 0 (unint w)) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)) (ite (< 0 0) true (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)))) (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)) (ite (is-cons v) (ite (is-cons w) (ite (is-int (car v)) (ite (is-int (car w)) (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (< (unint (car v)) (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< (unint (car v)) 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false))))) (ite (> (unint (car w)) 0) (ite (< 0 (unint (car w))) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))) (ite (< 0 0) true (ite (> (unint (car v)) 0) (ite (> (unint (car w)) 0) (ite (= (unint (car v)) (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= (unint (car v)) 0) (less-than (cdr v) (cdr w)) false)) (ite (> (unint (car w)) 0) (ite (= 0 (unint (car w))) (less-than (cdr v) (cdr w)) false) (ite (= 0 0) (less-than (cdr v) (cdr w)) false)))))) false) false) false) false)))
     (define-fun-rec ackermann-peter ((m Int) (n Int)) Int (ite (> m 0) (ite (> n 0) (ackermann-peter (- m 1) (ackermann-peter m (- n 1))) (ackermann-peter (- m 1) 1)) (+ n 1))))
   '((m . Int) (n . Int))
   '((> m 0) (> n 0))
   '(and (less-than (cons (int m) (int (- n 1)))
                    (cons (int m) (int n)))
         (less-than (cons (int (- m 1)) (int (ackermann-peter m (- n 1))))
                    (cons (int m) (int n))))))

;; EMACS ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; (put 'forall 'racket-indent-function 1)
;; (put 'declare-datatype 'racket-indent-function 1)
;; (put 'hash-for-each 'racket-indent-function 1)
