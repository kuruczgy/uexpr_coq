Require Import String.
Open Scope string_scope.
Require Import Coq.Lists.List.

Require Import Parser.
Require Import parser.

Definition str_map (X : Type) := list (prod string X).
Fixpoint str_map_get (X : Type) (m : str_map X) (k : string) : option X :=
match m with
| cons h t => if string_dec (fst h) k then Some (snd h) else str_map_get X t k
| nil => None
end.

Theorem test2 : (str_map_get nat (cons (pair "a" 1) nil) "b") = None.
reflexivity.
Qed.

Inductive uexpr_type : Set :=
| t_string
| t_boolean
(*| t_list*)
| t_void
| t_fn
| t_error.

Inductive uexpr_val : Set :=
| v_string : string -> uexpr_val
| v_boolean : bool -> uexpr_val
| v_void : uexpr_val
| v_fn : uexpr -> uexpr_val
| v_error : uexpr_val.

Definition uexpr_env := str_map uexpr_val.

Inductive uexpr_eval : uexpr_env -> uexpr -> uexpr_env -> uexpr_val -> Prop :=
| eval_string
  (n : uexpr_env)
  (s : string)
  : uexpr_eval n (e_string s) n (v_string s)
| eval_neg_on_bool
  (n1 n2 : uexpr_env)
  (b : bool)
  (e : uexpr)
  (H : uexpr_eval n1 e n2 (v_boolean b))
  : uexpr_eval n1 (e_unop unop_neg e) n2 (v_boolean (negb b))
| eval_eq_on_strings
  (n1 n2 n3 : uexpr_env)
  (s1 s2 : string)
  (e1 e2 : uexpr)
  (H1 : uexpr_eval n1 e1 n2 (v_string s1))
  (H2 : uexpr_eval n2 e2 n3 (v_string s2))
  : uexpr_eval n1 (e_binop binop_eq e1 e2) n3 (v_boolean (if string_dec s1 s2 then true else false)).
  
Fixpoint my_eval (fuel : nat) (n1 : uexpr_env) (e : uexpr)
  : option { n2 : uexpr_env & { v : uexpr_val & uexpr_eval n1 e n2 v } } :=
match fuel with
| S f =>
match e with
| e_string s => Some (existT _ n1 (existT _ (v_string s) (eval_string n1 s)))
| e_unop unop_neg e1 => match my_eval f n1 e1 with
    | Some (existT _ n2 (existT _ (v_boolean b) pf)) =>
      Some (existT _ n2 (existT _ (v_boolean (negb b)) (eval_neg_on_bool n1 n2 b e1 pf)))
    | _ => None
  end
| e_binop binop_eq e1 e2 => match my_eval f n1 e1 with
    | Some (existT _ n2 (existT _ (v_string s1) pf1)) => match my_eval f n2 e2 with
      | Some (existT _ n3 (existT _ (v_string s2) pf2)) =>
        Some (existT _ n3 (existT _ (v_boolean (if string_dec s1 s2 then true else false))
          (eval_eq_on_strings n1 n2 n3 s1 s2 e1 e2 pf1 pf2)))
      | _ => None
    end
    | _ => None
  end
| _ => None
end
| O => None
end.

Definition partialOut
  (n1 : uexpr_env)
  (e : uexpr)
  (x : option { n2 : uexpr_env & { v : uexpr_val & uexpr_eval n1 e n2 v } }) :=
  match x return
    (match x with
     | Some (existT _ nil (existT _ (v_boolean true) pf)) => uexpr_eval n1 e nil (v_boolean true)
     | _ => True
     end) with
  | Some (existT _ nil (existT _ (v_boolean true) pf)) => pf
  | _  => I
  end.

Definition res_to_option
  (T : Type)
  (x : @res T) :=
  match x with
  | Res v => Some v
  | Err _ => None
  end
.

Definition extract_option
  (T : Type)
  (x : option T) :=
  match x return
    match x with
    | Some _ => T
    | None => True
    end
  with
  | Some v => v
  | None => I
  end
.

Definition eval_e (fuel : nat) (e : uexpr) :=
  match my_eval fuel nil e with
  | Some (existT _ _ (existT _ v pf)) => Some v
  | _ => None
  end
.

Definition eval (fuel : nat) (s : string) :=
  match parse s with
  | Res e => eval_e fuel e
  | Err _ => None
  end
.

Compute (eval 100 "~(a=a)").

Theorem eval_e_correct :
  forall
    (e : uexpr)
    (fuel : nat)
    (v : uexpr_val),
    eval_e fuel e = Some v -> exists (n2 : uexpr_env), uexpr_eval nil e n2 v
.
Proof.
  intros.
  unfold eval_e in H.
  destruct (my_eval fuel nil e).
  - destruct s. destruct s. injection H as H. rewrite <- H. exists x. assumption.
  - discriminate H.
Qed.
