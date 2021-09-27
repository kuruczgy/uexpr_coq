Require Import String.

Inductive uexpr_unop : Set := | unop_neg.
Inductive uexpr_binop : Set :=
| binop_and
| binop_or
| binop_eq
| binop_incl.

Inductive uexpr : Set :=
| e_string : string -> uexpr
| e_block : list uexpr -> uexpr
| e_call : string -> list uexpr -> uexpr
| e_var : string -> uexpr
| e_unop : uexpr_unop -> uexpr -> uexpr
| e_binop : uexpr_binop -> uexpr -> uexpr -> uexpr.

