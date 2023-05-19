#lang racket/base

(require
 ffi/unsafe
 ffi/unsafe/define
 (only-in racket/match match-let*)
 (only-in cheesecake/macros Triple Tuple))
(provide
 (except-out (all-defined-out) define-z3))

(define-ffi-definer define-z3
  (ffi-lib "/Users/kartik/local/z3/lib/libz3"))

(define-cpointer-type _Z3_config)
(define-cpointer-type _Z3_context)
(define-cpointer-type _Z3_solver)
(define-cpointer-type _Z3_sort)
(define-cpointer-type _Z3_func_decl)
(define-cpointer-type _Z3_symbol)
(define-cpointer-type _Z3_ast)
(define-cpointer-type _Z3_ast_vector)
(define-cpointer-type _Z3_constructor)
(define-cpointer-type _Z3_model)
(define-cpointer-type _Z3_pattern)
(define-cpointer-type _Z3_tactic)
(define-cpointer-type _Z3_goal)
(define-cpointer-type _Z3_apply_result)

(define _Z3_lbool
  (_enum '(Z3_L_FALSE = -1
           Z3_L_UNDEF
           Z3_L_TRUE) 
         _int32))

(define _Z3_ast_kind
  (_enum '(Z3_NUMERAL_AST
           Z3_APP_AST
           Z3_VAR_AST
           Z3_QUANTIFIER_AST
           Z3_SORT_AST
           Z3_FUNC_DECL_AST
           Z3_UNKNOWN_AST = 1000)
         _int32))

(define _Z3_ast_print_mode
  (_enum '(Z3_PRINT_SMTLIB_FULL
           Z3_PRINT_LOW_LEVEL
           Z3_PRINT_SMTLIB2_COMPLIANT)
          _int32))

(define-z3 Z3_mk_config
  (_fun -> _Z3_config))

(define-z3 Z3_del_config
  (_fun _Z3_config -> _void))

(define-z3 Z3_set_param_value
  (_fun _Z3_config _string _string -> _void))

(define-z3 Z3_mk_context
  (_fun _Z3_config -> _Z3_context))

(define-z3 Z3_del_context
  (_fun _Z3_context -> _void))

(define-z3 Z3_mk_solver
  (_fun _Z3_context -> _Z3_solver))

(define-z3 Z3_solver_inc_ref
  (_fun _Z3_context _Z3_solver -> _void))

(define-z3 Z3_solver_dec_ref
  (_fun _Z3_context _Z3_solver -> _void))

(define-z3 Z3_mk_tactic
  (_fun _Z3_context _string -> _Z3_tactic))

(define-z3 Z3_tactic_and_then
  (_fun _Z3_context _Z3_tactic _Z3_tactic -> _Z3_tactic))

(define-z3 Z3_tactic_apply
  (_fun _Z3_context _Z3_tactic _Z3_goal -> _Z3_apply_result))

(define-z3 Z3_apply_result_get_num_subgoals
  (_fun _Z3_context _Z3_apply_result -> _uint))

(define-z3 Z3_apply_result_get_subgoal
  (_fun _Z3_context _Z3_apply_result _uint -> _Z3_goal))

(define-z3 Z3_mk_goal
  (_fun _Z3_context _stdbool _stdbool _stdbool -> _Z3_goal))

(define-z3 Z3_mk_int_sort
  (_fun _Z3_context -> _Z3_sort))

(define-z3 Z3_mk_bool_sort
  (_fun _Z3_context -> _Z3_sort))

(define-z3 Z3_mk_int_symbol
  (_fun _Z3_context _int -> _Z3_symbol))

(define-z3 Z3_mk_string_symbol
  (_fun _Z3_context _string -> _Z3_symbol))

(define-z3 Z3_mk_constructor
  (_fun (c name recognizer field-names sorts sort-refs) ::
        (c : _Z3_context) (name : _Z3_symbol) (recognizer : _Z3_symbol)
        (num-fields : _uint = (length field-names))
        (field-names : (_list i _Z3_symbol)) (sorts : (_list i _Z3_sort/null))
        (sort-refs : (_list i _uint)) -> _Z3_constructor))

(define-z3 Z3_query_constructor
  (_fun _Z3_context _Z3_constructor
        (num-fields : _uint) (constructor : (_ptr o _Z3_func_decl))
        (tester : (_ptr o _Z3_func_decl))
        (accessors : (_list o _Z3_func_decl num-fields)) -> _void ->
        (Triple constructor tester accessors)))

(define-z3 Z3_del_constructor
  (_fun _Z3_context _Z3_constructor -> _void))

(define-z3 Z3_mk_datatype
  (_fun (c name constructors) ::
        (c : _Z3_context) (name : _Z3_symbol)
        (num_constructors : _uint = (length constructors))
        (constructors : (_list i _Z3_constructor)) ->
        _Z3_sort))

(define-z3 Z3_mk_const
  (_fun _Z3_context _Z3_symbol _Z3_sort -> _Z3_ast))

(define-z3 Z3_mk_func_decl
  (_fun (c s domains range) ::
        (c : _Z3_context) (s : _Z3_solver)
        (domain_size : _uint = (length domains))
        (domains : (_list i _Z3_sort)) (range : _Z3_sort) -> _Z3_sort))

(define-z3 Z3_mk_pattern
  (_fun (c terms) ::
        (c : _Z3_context) (num_patterns : _uint = (length terms))
        (terms : (_list i _Z3_ast)) -> _Z3_pattern))

(define-z3 Z3_mk_rec_func_decl
  (_fun (c s domains range) ::
        (c : _Z3_context) (s : _Z3_symbol)
        (domain_size : _uint = (length domains)) (range : _Z3_sort) ->
        _Z3_func_decl))

(define-z3 Z3_add_rec_def
  (_fun (c f args body) ::
        (c : _Z3_context) (f : _Z3_func_decl) (n : _uint = (length args))
        (args : (_list i _Z3_ast)) (body : _Z3_ast) -> _void))

(define-z3 Z3_mk_forall
  (_fun (c weight patterns sorts decl_names body) ::
        (c : _Z3_context) (weight : _uint)
        (num_patterns : _uint = (length patterns))
        (patterns : (_list i _Z3_pattern))
        (num_decls : _uint = (length sorts))
        (decl_names : (_list i _Z3_symbol))
        (body : _Z3_ast) -> _Z3_ast))

(define-z3 Z3_mk_app
  (_fun (c d args) ::
        (c : _Z3_context) (d : _Z3_func_decl)
        (num_args : _uint = (length args)) (args : (_list i _Z3_ast)) ->
        _Z3_ast))

(define-z3 Z3_mk_eq
  (_fun _Z3_context _Z3_ast _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_ite
  (_fun _Z3_context _Z3_ast _Z3_ast _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_implies
  (_fun _Z3_context _Z3_ast _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_add
  (_fun (c args) :: (c : _Z3_context) (num_args : _uint = (length args))
        (args : (_list i _Z3_ast)) -> _Z3_ast))

(define-z3 Z3_mk_lt
  (_fun _Z3_context _Z3_ast _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_le
  (_fun _Z3_context _Z3_ast _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_gt
  (_fun _Z3_context _Z3_ast _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_ge
  (_fun _Z3_context _Z3_ast _Z3_ast -> _Z3_ast))

;; Example. (Z3_mk_solver_for_logic ctx (Z3_mk_string_symbol ctx "QF_LIA"))
(define-z3 Z3_mk_solver_for_logic
  (_fun _Z3_context _Z3_symbol -> _Z3_solver))

(define-z3 Z3_mk_not
  (_fun _Z3_context _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_and
  (_fun (context arguments) ::
        (context : _Z3_context) 
        (number-of-arguments : _uint = (length arguments))
        (arguments : (_list i _Z3_ast)) ->
        _Z3_ast))

(define-z3 Z3_mk_or
  (_fun (context arguments) ::
    (context : _Z3_context)
    (number-of-arguments : _uint = (length arguments))
    (arguments : (_list i _Z3_ast)) ->
      _Z3_ast))

(define-z3 Z3_mk_iff
  (_fun _Z3_context _Z3_ast _Z3_ast -> _Z3_ast))

(define-z3 Z3_mk_int
  (_fun _Z3_context _int _Z3_sort -> _Z3_ast))

(define-z3 Z3_mk_true
  (_fun _Z3_context -> _Z3_ast))

(define-z3 Z3_solver_assert
  (_fun _Z3_context _Z3_solver _Z3_ast -> _void))

(define-z3 Z3_solver_check
  (_fun _Z3_context _Z3_solver -> _Z3_lbool))

(define-z3 Z3_solver_check_assumptions
  (_fun (c s assumptions) ::
        (c : _Z3_context) (s : _Z3_solver)
        (num_assumptions : _uint = (length assumptions))
        (assumptions : (_list i _Z3_ast)) -> _Z3_lbool))

(define-z3 Z3_solver_get_model
  (_fun _Z3_context _Z3_solver -> _Z3_model))

(define-z3 Z3_model_eval
  (_fun _Z3_context _Z3_model _Z3_ast _stdbool (v : (_ptr o _Z3_ast)) ->
        (succeeded? : _stdbool) -> (Tuple succeeded? v)))

(define-z3 Z3_solver_get_unsat_core
  (_fun _Z3_context _Z3_solver -> _Z3_ast_vector))

(define-z3 Z3_solver_push
  (_fun _Z3_context _Z3_solver -> _void))

(define-z3 Z3_solver_pop
  (_fun _Z3_context _Z3_solver _uint -> _void))

(define-z3 Z3_solver_reset
  (_fun _Z3_context _Z3_solver -> _void))

(define-z3 Z3_get_ast_kind
  (_fun _Z3_context _Z3_ast -> _Z3_ast_kind))

(define-z3 Z3_set_ast_print_mode
  (_fun _Z3_context _Z3_ast_print_mode -> _void))

(define-z3 Z3_ast_to_string
  (_fun _Z3_context _Z3_ast -> _string))

(define-z3 Z3_solver_get_assertions
  (_fun _Z3_context _Z3_solver -> _Z3_ast_vector))

(define-z3 Z3_ast_vector_get
  (_fun _Z3_context _Z3_ast_vector _uint -> _Z3_ast))

(define-z3 Z3_ast_vector_size
  (_fun _Z3_context _Z3_ast_vector -> _uint))

#|
Creates a `Z3_context` object and a `Z3_solver` object. Please note that a
solver for just the "QF_LIA" logic or the "QF_UFLIA" logic might not yield
unsat for an assertion stack that is inconsistent in the theory of datatypes.
For example, `(declare-const v Value) (assert (is-nil v)) (assert (is-cons v))`
was deemed satisfiable in the aforementioned logics.

Declares the `Int` and `Bool` sorts.

Defines the recursive datatype `Value`.

Returns a list with four elements. The first is the `Z3_context` object, the
second is the `Z3_solver` object, the third is a function that maps symbols to
their `Z3_func_decl` counterparts, and the fourth is a function that maps
symbols to their `Z3_sort` counterparts.
|#
(define (open-Z3)
  (match-let*
      ((cfg (Z3_mk_config))
       (ctx (begin0
                (Z3_mk_context cfg)
              (Z3_del_config cfg)))
       (_ (Z3_set_ast_print_mode ctx 'Z3_PRINT_SMTLIB_FULL))
       (solv (Z3_mk_solver ctx))
       (_ (Z3_solver_inc_ref ctx solv))

       (Bool-sort (Z3_mk_bool_sort ctx))
       (Int-sort (Z3_mk_int_sort ctx))

       (nil-sym (Z3_mk_string_symbol ctx "nil"))
       (is-nil--sym (Z3_mk_string_symbol ctx "is-nil"))
       (nil-con (Z3_mk_constructor ctx nil-sym is-nil--sym null null null))

       (bool-sym (Z3_mk_string_symbol ctx "bool"))
       (is-bool--sym (Z3_mk_string_symbol ctx "is-bool"))
       (unbool-sym (Z3_mk_string_symbol ctx "unbool"))
       (bool--field-names (list unbool-sym))
       (bool--field-sorts (list Bool-sort))
       (bool--sort-refs (list 0))
       (bool-con (Z3_mk_constructor ctx bool-sym is-bool--sym bool--field-names
                                    bool--field-sorts bool--sort-refs))

       (int-sym (Z3_mk_string_symbol ctx "int"))
       (is-int--sym (Z3_mk_string_symbol ctx "is-int"))
       (unint-sym (Z3_mk_string_symbol ctx "unint"))
       (int--field-names (list unint-sym))
       (int--field-sorts (list Int-sort))
       (int--sort-refs (list 0))
       (int-con (Z3_mk_constructor ctx int-sym is-int--sym int--field-names
                                   int--field-sorts int--sort-refs))

       (cons-sym (Z3_mk_string_symbol ctx "cons"))
       (is-cons--sym (Z3_mk_string_symbol ctx "is-cons"))
       (car-sym (Z3_mk_string_symbol ctx "car"))
       (cdr-sym (Z3_mk_string_symbol ctx "cdr"))
       (cons--field-names (list car-sym cdr-sym))
       (cons--field-sorts (list #f #f))
       (cons--sort-refs (list 0 0))
       (cons-con (Z3_mk_constructor ctx cons-sym is-cons--sym cons--field-names
                                    cons--field-sorts cons--sort-refs))
       
       (Value-constructors (list nil-con bool-con int-con cons-con))
       (Value-sym (Z3_mk_string_symbol ctx "Value"))
       (Value-sort (Z3_mk_datatype ctx Value-sym Value-constructors))

       ((Triple nil-decl is-nil--decl _)
        (begin0
            (Z3_query_constructor ctx nil-con 0)
          (Z3_del_constructor ctx nil-con)))
       ((Triple bool-decl is-bool--decl (list unbool-decl))
        (begin0
            (Z3_query_constructor ctx bool-con 1)
          (Z3_del_constructor ctx bool-con)))
       ((Triple int-decl is-int--decl (list unint-decl))
        (begin0
            (Z3_query_constructor ctx int-con 1)
          (Z3_del_constructor ctx int-con)))
       ((Triple cons-decl is-cons--decl (list car-decl cdr-decl))
        (begin0
            (Z3_query_constructor ctx cons-con 2)
          (Z3_del_constructor ctx cons-con)))

       (sym->func-decl (hash
                        'nil nil-decl
                        'is-nil is-nil--decl
                        'bool-decl bool-decl
                        'is-bool is-bool--decl
                        'unbool unbool-decl
                        'int int-decl
                        'is-int is-int--decl
                        'unint unint-decl
                        'cons cons-decl
                        'is-cons is-cons--decl
                        'car car-decl
                        'cdr cdr-decl))

       (sym->sort (hash
                   'Bool Bool-sort
                   'Int Int-sort
                   'Value Value-sort)))

    (list ctx solv sym->func-decl sym->sort)))

#|
Decrements the reference counter of solver `solv` with respect to context
`ctx`, possibly making the solver available to the garbage collector.

Also deletes `ctx`.
|#
(define (close-Z3 ctx solv)
  (Z3_solver_dec_ref ctx solv)
  (Z3_del_context ctx))
