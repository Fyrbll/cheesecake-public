# Setup

Install Racket. Cheesecake has been written in and tested with Racket v8.7.0.6 [cs]

Install Z3 and make sure it is available through the `PATH` environment variable. Cheesecake has been tested with Z3 v4.8.15.

# Usage

## Translator for Typed Racket Types

The translator is defined in `translate.rkt`.

The function `(translate QUERY)` translates a subtyping query to an suitable input for Cheesecake.

`QUERY` is an expression of the form `(quasiquote (subtype? ,TAU1 ,TAU2))` where `TAU1` and `TAU2` are quoted expressions that represent types in Typed Racket. The grammar of these quoted expressions that represent types is

```
VARIABLE ::= <any Racket symbol without a special meaning in this grammar>

INTEGER ::= <any Racket integer>

UNARY ::= car | cdr | not | null? | boolean? | integer? | pair?

BINARY ::= cons | = | + | - | * | - | < | > | <= | >=

EXPRESSION ::= VARIABLE
             | null
             | #t | #f
             | INTEGER
             | (UNARY EXPRESSION)
             | (BINARY EXPRESSION EXPRESSION)
             | (if EXPRESSION EXPRESSION EXPRESSION)
             | (: EXPRESSION TYPE)

TYPE ::= VARIABLE
       | Nothing
       | Null
       | Boolean
       | Integer
       | (Pair TYPE TYPE)
       | (TYPE -> TYPE)
       | (Rec VARIABLE TYPE)
       | (Union TYPE TYPE)
       | (Intersection TYPE TYPE)
       | (Refine (VARIABLE : TYPE) EXPRESSION)
       | Any
```

Running the simple translation `(translate '(subtype? (Refine (x : Integer) (> x 0)) Integer))` prints the following form to the default output port.

```
(prove (forall ((v Value)) (=> (and (is-int v) (unbool_ (bool (> (unint_ v) (unint_ (int 0)))))) (is-int v))))
```

The entire output of the `translate` function can be saved to a file and loaded into Cheesecake according to the instructions in the next section.

Example queries with more complicated types have been provided in `translate.rkt`.

## Theorem Prover (Cheesecake)

To use Cheesecake, start its REPL by running `racket repl.rkt` in your shell. It will print the number of goals in the goal list, which is initially 0, as part of its input prompt.

```
$ racket repl.rkt
0 goals -> 
```

The next step is to load an input file. To load the file `test-10`, run `(load "test-10")`. To check the goal that was loaded, run the `(print-goal)` command.

```
0 goals -> (load "test-10")
last command took 823 ms
1 goals -> (print-goal)
[forall] in-even : Int, v : Value
[to prove]
(is-natural v)
[assuming]
(is-odd-even in-even v)
[schemes used] ()
last command took 0 ms
1 goals ->
```

To see if Cheesecake can prove this goal automatically, run `(automatic)`. If it finds a proof, it will print a proof script that leads to a state with no remaining goals.

```
1 goals -> (automatic)
[success]
(induct (is-odd-even in-even v))
(prove)
(prove)
(prove)
last command took 484 ms
0 goals ->
```

There are two main ways to configure the `(automatic)` command. The first is to set a timeout for each call to the SMT solver with `(set-timeout N)` where `N` is the number of milliseconds after which the solver should give up.

```
0 goals -> (set-timeout 5000)
0 goals ->
```

Another way is to use the optional argument `gas`, which controls how many steps the backtracking prover will run for before reporting failure. The default value of `gas` is 20.

```
0 goals -> (load "test-10")
1 goals -> (automatic 2)
[out of gas]
(induct (is-odd-even in-even v))
(prove)
last command took 403 ms
2 goals -> (automatic 10)
[success]
(prove)
(prove)
last command took 101 ms
0 goals ->
```

Once the session is complete (all goals are proved), Cheesecake can be quit by running `(exit)`

```
0 goals -> (exit)
last command took 18 ms
```

A command list for users who are interested in trying the prover themselves:

- `(load FILE)` loads a file into the prover
- `(exit)` quits the prover
- `(forward)` makes the next goal in the goal list active
- `(backward)` makes the previous goal in the goal active
- `(print-goal)` prints the active goal
- `(automatic [GAS])` applies backtracking search to find a successful proof
- `(induct EXPRESSION)` inducts according to a well-founded relation derived from a call to a recursive function that is a subexpression of the goal
- `(eliminate-destructors)` splits the goal so that paths like `(car x)` and `(cdr x)` are replaced with fresh variables
- `(prove)` uses the backend SMT solver, currently Z3, to prove the current goal non-inductively
- `(undo)` undoes the most recent successful 
- `(suggest)` inspects the goal and reports possible function calls to use `(induct _)`  with