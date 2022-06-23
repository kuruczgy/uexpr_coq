Require Import String.
Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Parser.
Require Import parser.

Definition str_map (X : Type) := list (prod string X).
Fixpoint str_map_get (X : Type) (m : str_map X) (k : string) (def : X) : X :=
match m with
| cons h t => if string_dec (fst h) k then snd h else str_map_get X t k def
| nil => def
end.

Inductive uexpr_type : Set :=
| t_string
| t_boolean
| t_list
| t_void
| t_fn
| t_error.

Inductive uexpr_val : Set :=
| v_string : string -> uexpr_val
| v_boolean : bool -> uexpr_val
| v_list : list uexpr_val -> uexpr_val
| v_void : uexpr_val
| v_fn : uexpr -> uexpr_val
| v_error : uexpr_val.

Definition uexpr_env := str_map uexpr_val.

Inductive uexpr_eval : uexpr_env -> uexpr -> uexpr_env -> uexpr_val -> Prop :=
| eval_string
  (n : uexpr_env)
  (s : string)
  : uexpr_eval n (e_string s) n (v_string s)
| eval_block_empty
  (n : uexpr_env)
  : uexpr_eval n (e_block nil) n (v_void)
| eval_block_single
  (n_1 n_2 : uexpr_env)
  (e : uexpr)
  (v : uexpr_val)
  (H : uexpr_eval n_1 e n_2 v)
  : uexpr_eval n_1 (e_block (cons e nil)) n_2 v
| eval_block_cons
  (n_head_1 n_head_2 n_tail_2 : uexpr_env)
  (e_head e_tail_h : uexpr)
  (e_tail_t : list uexpr)
  (v_head v_tail : uexpr_val)
  (H_head : uexpr_eval n_head_1 e_head n_head_2 v_head)
  (H_tail : uexpr_eval n_head_2 (e_block (e_tail_h :: e_tail_t)) n_tail_2 v_tail)
  : uexpr_eval n_head_1 (e_block (e_head :: e_tail_h :: e_tail_t)) n_tail_2 v_tail
| eval_call
  (n_1 n_2 : uexpr_env)
  (var : string)
  (e : uexpr)
  (v : uexpr_val)
  (H_eval : uexpr_eval n_1 e n_2 v)
  (H_get : str_map_get _ n_1 var v_error = v_fn e)
   : uexpr_eval n_1 (e_call var []) n_2 v
| eval_var
  (var : string)
  (n : uexpr_env)
  : uexpr_eval n (e_var var) n (str_map_get _ n var v_error)
| eval_neg
  (n1 n2 : uexpr_env)
  (v : uexpr_val)
  (e : uexpr)
  (H : uexpr_eval n1 e n2 v)
  : uexpr_eval n1 (e_unop unop_neg e) n2 (
    match v with
    | v_boolean b => v_boolean (negb b)
    | _ => v_error
    end)
| eval_eq_on_strings
  (n1 n2 n3 : uexpr_env)
  (s1 s2 : string)
  (e1 e2 : uexpr)
  (H1 : uexpr_eval n1 e1 n2 (v_string s1))
  (H2 : uexpr_eval n2 e2 n3 (v_string s2))
  : uexpr_eval n1 (e_binop binop_eq e1 e2) n3 (v_boolean (if string_dec s1 s2 then true else false))
| eval_let
  (n1 n2 : uexpr_env)
  (var : string)
  (e : uexpr)
  (v : uexpr_val)
  (H : uexpr_eval n1 e n2 v)
  : uexpr_eval n1 (e_call "let" [e_var var; e]) ((var, v) :: n2) (v_void)
| eval_let_fn
  (n : uexpr_env)
  (var : string)
  (e : uexpr)
   : uexpr_eval n (e_call "let_fn" [e_var var; e]) ((var, v_fn e) :: n) (v_void)
.

Definition my_eval : forall
  (fuel : nat)
  (n1 : uexpr_env)
  (e : uexpr),
  option { n2 : uexpr_env & { v : uexpr_val & uexpr_eval n1 e n2 v } }.
Proof.
  refine (fix my_eval (fuel : nat) (n1 : uexpr_env) (e : uexpr)
  : option { n2 : uexpr_env & { v : uexpr_val & uexpr_eval n1 e n2 v } } :=
match fuel with
| S f =>
match e with
| e_string s => Some (existT _ n1 (existT _ (v_string s) (eval_string n1 s)))
| e_block nil => Some (existT _ n1 (existT _ (v_void) (eval_block_empty n1)))
| e_block (e1 :: nil) =>
    match my_eval f n1 e1 with
    | Some (existT _ n2 (existT _ v pf)) =>
        Some (existT _ n2 (existT _ v (eval_block_single n1 n2 e1 v pf)))
    | _ => None
    end
| e_block (e_head :: e_tail_h :: e_tail_t) =>
    match my_eval f n1 e_head with
    | Some (existT _ n_head_2 (existT _ v_head H_head)) =>
        match my_eval f n_head_2 (e_block (e_tail_h :: e_tail_t)) with
        | Some (existT _ n_tail_2 (existT _ v_tail H_tail)) =>
            Some (existT _ n_tail_2 (existT _ v_tail (
              eval_block_cons n1 n_head_2 n_tail_2 e_head e_tail_h e_tail_t v_head v_tail H_head H_tail
            )))
        | _ => None
        end
    | _ => None
    end
| e_var var =>
    Some (existT _ n1 (existT _ (str_map_get _ n1 var v_error) (
      eval_var var n1
    )))
| e_unop unop_neg e1 =>
    match my_eval f n1 e1 with
    | Some (existT _ n2 (existT _ v pf)) =>
      Some (existT _ n2 (existT _ (
    match v with
    | v_boolean b => v_boolean (negb b)
    | _ => v_error
    end) (eval_neg n1 n2 v e1 pf)))
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
| e_call "let" [e_var var; e1] =>
    match my_eval f n1 e1 with
    | Some (existT _ n2 (existT _ v H)) =>
        Some (existT _ ((var, v) :: n2) (existT _ v_void (
          eval_let n1 n2 var e1 v H
        )))
    | _ => None
    end
| e_call "let_fn" [e_var var; e1] =>
    Some (existT _ ((var, v_fn e1) :: n1) (existT _ v_void (
      eval_let_fn n1 var e1
    )))
| e_call var [] =>
    let get_res := str_map_get _ n1 var v_error in
    let H_get : str_map_get _ n1 var v_error = get_res := eq_refl get_res in
    (match get_res with
    | v_fn e =>
        fun H_get => match my_eval f n1 e with
        | Some (existT _ n_2 (existT _ v H_eval)) =>
            Some (existT _ n_2 (existT _ v (
            eval_call n1 n_2 var e v H_eval H_get
            )))
        | _ => None
        end
    | _ => fun _ => None
   end H_get)
| _ => None
end
| O => None
end).
Defined.

Definition eval_e (fuel : nat) (e : uexpr) :=
  match my_eval fuel nil e with
  | Some (existT _ n (existT _ v pf)) => Some (n, v)
  | _ => None
  end
.

Theorem eval_e_correct :
  forall
    (e : uexpr)
    (fuel : nat)
    (n : uexpr_env)
    (v : uexpr_val),
    eval_e fuel e = Some (n, v) -> uexpr_eval nil e n v
.
Proof.
  intros.
  unfold eval_e in H.
  destruct (my_eval fuel nil e).
  - destruct s. destruct s. injection H as H. rewrite <- H. rewrite <- H0. assumption.
  - discriminate H.
Qed.


Definition eval (fuel : nat) (s : string) :=
  match parse s with
  | Res e => eval_e fuel e
  | Err _ => None
  end
.

Compute (eval 100 "{x; y; z; ~(a=a); end;}").
