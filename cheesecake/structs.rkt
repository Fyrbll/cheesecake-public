#lang racket/base

(require
 (for-syntax
  (only-in racket/base #%app #%datum lambda syntax syntax-case with-syntax)
  (only-in racket/syntax format-id))
 (only-in racket/list range))
(provide (all-defined-out))

#|
Represents the global state of the prover.
FUNS is a list of non-recursive function definitions.
RECFUNS is a list of recursive function definitions.
GOALS-HIST is the history of conjunctions of goals as well as the goal we are
pointing at. Suppose our conjunction begins with a single goal and we are
pointing at index 0. Tactics can be used to turn that goal into a conjunction
(list) of goals. As soon as the goal is transformed, we cons the new conjunction
on to the old GOALS-HIST, so that an undo operation in the REPL corresponds to
replacing GOALS-HIST with its own cdr. It matches the structure
(:: (Tuple (GOAL GOALS ...) CURSOR) GOALS-HIST ...)
PROC is a Process struct, which represents a Z3 process.
|#
(struct Env (funs recfuns goals-hist proc) #:mutable #:transparent)

(define Env--goals-hist
  Env-goals-hist)

(define set-Env--goals-hist!
  set-Env-goals-hist!)

(define (update-Env-funs! env updater)
  (set-Env-funs! env (updater (Env-funs env))))

(define (update-Env-recfuns! env updater)
  (set-Env-recfuns! env (updater (Env-recfuns env))))

(define (Env-recfuns-cons! env v)
  (set-Env-recfuns! env (cons v (Env-recfuns env))))

(define (update-Env--goals-hist! env updater)
  (set-Env--goals-hist! env (updater (Env--goals-hist env))))

#|
Represents a non-recursive function definition.

(define-fun NAME ((FORMALS DOMAINS) ...) RANGE
  BODY)
|#
(struct Fun (id formals doms rng body) #:transparent)

#|
Represents a recursive function definition with optional, extra information
related to termination checking (MEASUREDS, MEASURE, RELATION), an induction
template (MEASUREDS, TIPS), and quantifier patterns (PATTERNS).

(define-fun-rec NAME ((FORMALS DOMAINS) ...) RANGE
  BODY)

(declare-fun NAME (DOMAINS ...) RANGE)
(assert (forall ((FORMALS DOMAINS) ...) (!
  (= (NAME FORMALS ...) BODY)
  :patterns (PATTERNS ...))))

The element at the i-th index of MEASURED is #t if the i-th element of FORMALS
is mentioned in MEASURE.

RELATION should be a well founded relation. The measure of the formals should
be strictly greater than the measure of the actuals at each recursive call in
BODY.
|#
(struct RecFun (id formals measureds doms rng body tips indn pats meas reln)
  #:transparent)

#|
Represents a collection of recursive calls within some function body, stored as
ACTUALS*, which is the list of arguments to the recursive calls. Also stores
the tests that govern that collection of recursive calls in the list TESTS.
|#
(struct Tip (tests actuals*) #:transparent)
(define Tip-substns Tip-actuals*)
(define (Tip-substns-set tip substns)
  (struct-copy Tip tip (actuals* substns)))

#|
Represents a singular goal. It stands for the obligation

(forall ((FORMALS DOMS) ...)
  (=> FA-PREMS ... PREMS ... CONCL))

FA-PREMS is a list of universally quantified premises that will most likely
have to be dealt with using manual unification-based instantiation or
e-matching.
|#
(struct Goal (formals doms fa-prems prems concl schemes) #:transparent)
(define Goal--fa-prems Goal-fa-prems)

#|
Represents a Z3 process.
IN is an output port from Racket's perspective.
OUT is an input port from Racket's perspective.
PID is the process id of the given instance of Z3.
SIG-SND is a function that can be used to query the state of Z3 and also kill
it if necessary.
|#
(struct Process (id in out err sig-snd) #:transparent)

(define Process--sig-snd Process-sig-snd)

#|
The following code is unused at the moment: 
|#

#|
(env-apply ENV-STX FIELD-STX FUN-STX) applies the function FUN-STX to the value
at the field named FIELD-STX in the boxed Env struct ENV-STX.

(env-apply (box (Env 1 2 3 4)) fun (lambda (x) (+ x 5))) evaluates to 6
|#
(define-syntax env-apply
  (lambda (stx)
    (syntax-case stx ()
      ((_ env-stx field-stx fun-stx)
       (with-syntax
         ((accessor-stx (format-id (syntax field-stx) "Env-~a"
                                   (syntax field-stx))))
         (syntax (fun-stx (accessor-stx (unbox env-stx)))))))))

#|
(env-update! ENV-STX FIELD-STX FUN-STX) applies the function FUN-STX to the
value at the field named FIELD-STX in the boxed Env struct ENV-STX, creates
a new copy of ENV-STX with where the value at FIELD-STX has been replaced with
(FUN-STX FIELD-STX), and places this copy of ENV-STX inside the box.

(env-update! (box (Env 1 2 3 4)) recfun (lambda (x) (+ x 5)))
(env-apply (box (Env 1 2 3 4)) recfun identity) evaluates to 7
|#
(define-syntax env-update!
  (lambda (stx)
    (syntax-case stx ()
      ((_ env-stx field-stx fun-stx)
       (with-syntax
         ((accessor-stx (format-id (syntax field-stx) "Env-~a"
                                   (syntax field-stx))))
         (syntax
          (let* ((env (unbox env-stx))
                 (old (accessor-stx env)))
            (set-box! env-stx
                      (struct-copy Env env (field-stx (fun-stx old)))))))))))

#|
Within a `Tip`, a test expression is wrapped in `Req` when it should not be
removed during revision.
|#
(struct Req (expr))


#|
Struct representing a variable identified by its de Bruijn index.
Potentially for use in functions and universally quantified statements.
|#
(struct BV (idx))


#| Represents an induction scheme.
;; CALL has the form (FUNCTION . ARGUMENTS) where FUNCTION is a symbol and
;; ARGUMENTS is a list of expressions.
;; CASES is a list of Tip structs that represent the subgoals.
;; TESTS* is just map(Tip-tests, drop-right(CASES, 1)) where 'drop-right' 
;; discards the base case.
;; SUBSTITUTIONS is append-map(Tip-actuals*, CASES).
;; CHANGING is map(car, first(SUBSTITUTIONS)), as  all substitutions have the
;; same domain.
;; UNCHANGING is filter-not(curryr(member, CHANGING), formals) where 'formals'
;; is the list of formals of the goal at point.
;; SCORE is #f for the time being.
|#
(struct Scheme (calls cases tests* substitutions changing unchanging score))

(define (Scheme-displayln scheme)
  (printf "[calls] ~a~n" (Scheme-calls scheme))
  (displayln "[tests*]")
  (let ((tests* (Scheme-tests* scheme)))
    (for ((tests tests*)
          (tests-number (range 1 (+ (length tests*) 1))))
      (printf "~a. ~a~n" tests-number tests)))
  (displayln "[substns]")
  (let ((substns (Scheme-substitutions scheme)))
    (for ((substn substns)
          (substn-number (range 1 (+ (length substns) 1))))
      (printf "~a. φ[" substn-number)
      (let* ((pairs-count (length substn)))
        (for ((pair substn)
              (pair-number (range pairs-count)))
          (printf "~a/~a" (cdr pair) (car pair))
          (unless (equal? pair-number (- pairs-count 1))
            (display ","))))
      (displayln "]")))
  (printf "[changing] ~a~n" (Scheme-changing scheme))
  (printf "[unchanging] ~a~n" (Scheme-unchanging scheme))
  (printf "[score] ~a~n" (Scheme-score scheme)))

(define (Scheme--greater-than? scheme1 scheme2)
  (> (Scheme-score scheme1) (Scheme-score scheme2)))


(struct Decn (cont hist) #:transparent)


(struct Cmd (symb _thunk) #:transparent)

;; results from the solver
(struct solver-result ())
(struct unsat solver-result (core))
(struct sat solver-result ())
(struct unknown solver-result ())
