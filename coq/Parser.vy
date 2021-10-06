%{

Require Import String.

Inductive uexpr_unop : Set := | unop_neg.
Inductive uexpr_binop : Set :=
| binop_and
| binop_or
| binop_eq
| binop_incl
.

Inductive uexpr : Set :=
| e_string : string -> uexpr
| e_block : list uexpr -> uexpr
| e_list : list uexpr -> uexpr
| e_call : string -> list uexpr -> uexpr
| e_var : string -> uexpr
| e_unop : uexpr_unop -> uexpr -> uexpr
| e_binop : uexpr_binop -> uexpr -> uexpr -> uexpr
.

%}

%token EOF
%token LPAREN "(" RPAREN ")"
%token LBRACE "{" RBRACE "}"
%token LSQUARE "[" RSQUARE "]"
%token COMMA "," SEMI ";"
%token DOLLAR "$"
%token NOT "~" AND "&" OR "|" EQ "=" IN "%"
%token<string> STR

%start<uexpr> parse_uexpr
%type<uexpr> expr primary_expr unary_expr binary_expr
%type<list uexpr> list(";", expr) list(",", expr)
%type<uexpr_unop> unop
%type<uexpr_binop> binop

%%

let parse_uexpr := e = expr; EOF; { e }

let list(delim, x) :=
	| { nil }
	| h = x; { cons h nil }
	| h = x; delim; t = list(delim, x); { cons h t }

let unop := "~"; { unop_neg }
let binop :=
	| "&"; { binop_and }
	| "|"; { binop_or }
	| "="; { binop_eq }
	| "%"; { binop_incl }

let expr := binary_expr
let primary_expr :=
	| s = STR; <e_string>
	| "["; l = list(",", expr); "]"; <e_list>
	| "{"; l = list(";", expr); "}"; <e_block>
	| s = STR; "("; l = list(",", expr); ")"; { e_call s l }
	| "("; e = expr; ")"; { e }
	| "$"; s = STR; <e_var>
let unary_expr :=
	| primary_expr
	| o = unop; e = unary_expr; { e_unop o e }
let binary_expr :=
	| unary_expr
	| e1 = binary_expr; o = binop; e2 = unary_expr; { e_binop o e1 e2 }
