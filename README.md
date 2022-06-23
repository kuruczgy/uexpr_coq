# An attempt at formalizing my `uexpr` language in Coq

The "informal" language specification can be found in `spec.md`. You can find
the original C implementation of this language
[here](https://github.com/kuruczgy/gui_calendar/tree/master/src/uexpr).

First, a verified parser is build for this language. The grammar specification
can be found in `coq/Parser.vy`. The heavy lifting is then done by menhir,
which from the specification generates a parser written in Coq, along with a
proof of correctness. The `coq/parser.v` file contains some supporting
functions (such as the tokenizer), and exports a single `parse` function
combining the tokenizer and the parser.

The `uexpr.v` file contains the formal evaluation semantics definition as the
single `uexpr_eval` inductive type. This is basically a relation that relates
an expression with a value it evaluates to (along with the changes in the
environment).

The function `my_eval` is a verified interpreter that evaluates an expression,
and along with the results, returns a proof that `uexpr_eval` relates the
expression and its result.

The theorem `eval_e_correct` is then proved as an easy corollary using the
proof returned by `my_eval`.

Note that these proofs say nothing about non-terminating programs, or whether
the interpreter returns a result for terminating programs. Future work could
include extending the proofs for non-terminating programs, but this would
probably require changing the structure of the evaluation relation.

## Building
The parser is generated with menhir's coq backend. Run `menhir --coq
coq/Parser.vy` to generate `Parser.v`.
