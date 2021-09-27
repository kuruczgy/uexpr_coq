From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List.
Require Import Nat.
Import ListNotations.
Open Scope bool_scope.

Require Import ast.

Inductive token :=
  | TokString : string -> token
  | TokOp : ascii -> token.

Inductive res {X : Type} :=
  | Res : X -> res
  | Err : string -> res.

Definition head (s : string) := get 0 s.

Definition isWhite (c : ascii) : bool :=
  match nat_of_ascii c with
  | 32 => true (* space *)
  | 9 => true (* tab *)
  | 10 => true (* linefeed *)
  | 13 => true (* Carriage return. *)
  | _ => false
  end.
Definition isIdentChar (c : ascii) : bool :=
  let n := nat_of_ascii c in
  ((48 <=? n) && (n <=? 57)) ||
  ((65 <=? n) && (n <=? 90)) ||
  ((97 <=? n) && (n <=? 122)).

Definition string_includes (s : string) (c : ascii) : bool :=
  if find (Ascii.eqb c) (list_ascii_of_string s) then true else false.

Definition isOpChar (c : ascii) := string_includes "()[]{},$~&|=%;," c.

Fixpoint split_while (f : ascii -> bool) (s : string) : string * string :=
  match s with
  | EmptyString => (EmptyString, EmptyString)
  | String c s' =>
      if f c then
        match split_while f s' with
        | (x, y) => (String c x, y)
        end
      else
        (EmptyString, s)
  end.

Compute (split_while (fun c => (isOpChar c) && true) "()asd()").

Fixpoint tokenize (s : string) : @res (list token) :=
  match s with
  | EmptyString => Res []
  | String c s' =>
      if isWhite c then
        tokenize s'
      else if isOpChar c then
        match tokenize s' with
        | Err x => Err x
        | Res tks => Res ((TokOp c) :: tks)
        end
      else if Ascii.eqb c """" then
        tokenize_string s' [] true
      else if isIdentChar c then
        let cont := fun c =>
          match tokenize s' with
          | Err x => Err x
          | Res tks => Res ((TokString (String c EmptyString)) :: tks)
          end
        in
        match s' with
        | EmptyString => cont c
        | String c' s'' =>
          if isIdentChar c' then
            tokenize_string s' [c] false
          else
            cont c
        end
      else
        Err "can't match char"
  end
with tokenize_string
  (s : string)
  (acc : list ascii)
  (quoted : bool)
  {struct s}
  : @res (list token) :=
  let cont := fun s' acc =>
    match tokenize s' with
    | Err x => Err x
    | Res tks => Res ((TokString (string_of_list_ascii (rev acc))) :: tks)
    end
  in
  match s with
  | EmptyString => Err "unexpected end of string"
  | String c s' =>
    if quoted then
      match c with
      | """"%char => cont s' acc
      | c => tokenize_string s' (c :: acc) quoted
      end
    else
      if
        match s' with
        | EmptyString => false
        | String c' _ => isIdentChar c'
        end
      then
        tokenize_string s' (c :: acc) quoted
      else
        cont s' (c :: acc)
  end
.

Fixpoint parse_expr (tks : list token) : @res uexpr :=
  match tks with
  | (TokString s) :: tks' => Res (e_string s)
  | (TokOp "(") :: tks' => Err "n"
  | _ => Err "not implemented"
  end
.

Compute (
  let r := tokenize "{ let($a, t); ($a=t) & print(hello) }" in
  match r with
  | Err x => Err x
  | Res tks => parse_expr tks
  end
).

Require Extraction.
Recursive Extraction tokenize.

