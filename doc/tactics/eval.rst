========================================================================
Commands: `eval` and `check`
========================================================================

The ``eval`` and ``check`` commands execute closed expressions and
concrete procedures. They make specifications *testable*: a
specification written as operators (or as an imperative module) can be
run on known test vectors, in the same file, before anything is proved
about it.

.. admonition:: Syntax

  | ``eval`` *expr* ``.``
  | ``eval proc`` *M.f* ``(`` *args* ``) .``
  | ``check`` *expr* ``.``
  | ``check proc`` *M.f* ``(`` *args* ``) =`` *expr* ``.``

``eval`` prints the value of an expression, or the result of a call
to a procedure. ``check`` evaluates a boolean expression and fails
unless it is true; on an equality, both sides are printed when they
differ. ``check proc`` compares the result of a call with the value of
an expression, which makes differential testing of an imperative
implementation against a functional specification a one-liner.

Since ``check`` is a command that fails, ``fail check ...`` can be used
to test that an expression does not hold.

.. ecproof::
   :title: Evaluation Example

   require import AllCore List IntDiv.

   op fact (n : int) = foldl ( * ) 1 (range 1 (n + 1)).

   eval fact 20.
   check fact 5 = 120.
   check map (fun x => x %% 3) (iota_ 0 6) = [0; 1; 2; 0; 1; 2].

   module M = {
     proc fact(n : int) : int = {
       var r;
       r <- 1;
       while (0 < n) { r <- r * n; n <- n - 1; }
       return r;
     }
   }.

   check proc M.fact(10) = fact 10.

------------------------------------------------------------------------
What can be evaluated
------------------------------------------------------------------------

Evaluation is call-by-value and untyped. Values are integers (of
arbitrary size), booleans, tuples, values of datatypes and records,
functions, and the bitstrings of bound types (see below). The
evaluator

- computes the integer and boolean operators of the core library
  natively (``/\``, ``\/``, ``&&``, ``||`` and ``=>`` are lazy in
  their second argument), as well as ``iteri`` (hence ``iter`` and
  ``fold``), ``^`` and ``modexp``;

- computes natively, on lists whose elements are all known, the list
  functions ``size``, ``nth``, ``take``, ``drop``, ``++``, ``catrev``
  (hence ``rev``), ``map``, ``filter``, ``foldr`` and ``iota_``, and
  the bit encodings ``int2bs`` and ``bs2int`` of ``BitEncoding.BS2Int``;

- unfolds the definitions of operators, including operators defined
  by pattern matching, abbreviations and predicates. Within a command,
  the applications of operators defined by a body are memoised: their
  arguments are compared structurally (constructors with their type),
  except for the applications of abstract operators (such as arrays),
  compared by identity, and for functions nested in arguments, also
  compared by identity; applications to functions are not memoised.
  For instance, a sponge that squeezes its output again from the start
  for each output block computes each permutation once. Setting the
  environment variable ``EC_EVAL_NOMEMO`` disables this;

- represents the values of a ``subtype`` by their underlying value:
  ``insub`` checks the predicate, ``val`` is the identity;

- runs procedures: assignments, calls, conditionals, ``while`` loops
  and ``match``. Procedure arguments and local variables live in the
  frame of the call; module variables are global to one ``eval`` or
  ``check`` command, and start uninitialized. A function built by an
  expression (e.g. ``fun i => x + i``) sees the variables as they were
  when the expression was evaluated.

Equality is decided structurally, except that it is componentwise on
tuples and that it can be given, for a type, by rules of the ``eval``
database whose left-hand side is an equality at that type (see
below). This is how values represented by functions, such as arrays,
are compared.

Evaluation fails, with a message, on anything that has no
computational content: a quantifier, an application of an abstract
operator that no rule computes (see below), an equality between
functions, ``witness``, the read of an uninitialized variable, a
random sampling, or an abstract procedure. The message lists the
operators that were being evaluated, innermost first.

Evaluation does not necessarily terminate. The number of function
applications of an evaluation can be bounded with

.. admonition:: Syntax

  ``pragma Eval:steps =`` *n* ``.``

after which the ``eval`` and ``check`` commands fail when they exceed
*n* steps (*n* = 0, the default, means no bound). The count is
deterministic: it does not depend on the machine.

------------------------------------------------------------------------
The ``eval`` rule database
------------------------------------------------------------------------

Abstract operators, and operators whose definition is not executable
(it uses ``choiceb``, or is too inefficient), are computed with the
lemmas of the ``eval`` simplification database:

.. admonition:: Syntax

  ``hint simplify in eval :`` *lemma*\ :sub:`1` ``,`` ... ``,`` *lemma*\ :sub:`n` ``.``

Each lemma is an equation ``f p1 ... pn = e``, possibly under
hypotheses. When the evaluator meets ``f`` applied to values that
match the patterns ``p1 ... pn`` and the hypotheses evaluate to
``true``, it evaluates ``e`` instead. The rules of the database take
precedence over the definition of an operator. An abstract operator
with no rule in the ``eval`` database is computed with the rules of
the default simplification database (``hint simplify``), if any; when
no rule applies, its applications are kept as they are, and other
rules may still match them. The functions given as arguments to such
applications are memoised, so that, for instance, each element of an
array ``init f`` is computed once.

A lemma ``(a = b) <=> e``, where ``a`` and ``b`` are variables of a
type ``t``, defines the equality of the values of ``t``: for
instance ``(a = b) <=> (to_list a = to_list b)`` for an array type.

The standard library declares the rules ``iota_E`` (``List.Iota``),
``exp_modexp`` and ``exp_neg_eval`` (exponentiation in ``ZModP``, by
square-and-multiply, through an inversion for negative exponents),
``inv_eval`` (inversion in a ``ZModField``, by Fermat's little
theorem) and ``ilog_eval`` (``RealExp.ilog``, defined with real
logarithms, on integers).

.. ecproof::
   :title: Rule Example

   require import AllCore.

   op succ : int -> int.
   axiom succE x : succ x = x + 1.

   hint simplify in eval : succE.

   check succ 41 = 42.

------------------------------------------------------------------------
Bitstrings
------------------------------------------------------------------------

The types bound with ``bind bitstring`` (see the `bind` command) are
represented natively as bit-vectors, and so are the operators bound
with ``bind op`` to one of ``add``, ``sub``, ``mul``, ``opp``, ``and``,
``or``, ``xor``, ``not``, ``get`` and ``init``. When ``bool`` itself is
bound as a 1-bit bitstring, its values remain booleans.

------------------------------------------------------------------------
Trusted base
------------------------------------------------------------------------

The commands do not produce proofs and cannot be used to prove
anything. What an evaluation relies on is: the evaluator itself, the
native implementations of the core operators, and the equations it
uses: the rules of the simplification databases (lemmas), and the
side conditions of the ``bind`` commands (lemmas as well, unless they
were admitted).

------------------------------------------------------------------------
Profiling
------------------------------------------------------------------------

When the environment variable ``EC_EVAL_PROFILE`` is set, each
``eval`` and ``check`` command prints on the standard error the
number of steps it used, the operators that it applied most often,
with their number of applications, and the operators whose
applications were memoised, with their numbers of hits and misses.
