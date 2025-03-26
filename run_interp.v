Require Import Coq.Program.Wf.
Require Import List.
Import ListNotations.

Definition var := nat.
Definition value := nat.
Definition vars := list value.

Inductive stmt : Type :=
| break : nat -> stmt
| set : var -> value -> stmt
| block : list stmt -> stmt.

Definition cfg := (vars * stmt)%type.

(* These two will have to be defined before animation, probably *)
Axiom measure_cfg : cfg -> nat.
Axiom measure_cfg_wf : well_founded (MR lt measure_cfg).
(* This will be a proof obligation in every case it is used *)
Axiom fill_here : forall (c1 c2 : cfg), (MR lt measure_cfg) c1 c2.

(* Fixpoint even (n : nat) : bool := *)
(*   match n with *)
(*   | O => true *)
(*   | S n' => odd n' *)
(*   end *)
(* with odd (n : nat) : bool := *)
(*   match n with *)
(*   | O => false *)
(*   | S n' => even n' *)
(*   end. *)

(* Goal forall n, {even n = true}+{odd n = true}. *)
(*   intros n. *)
(*   induction n. *)
(*   left; auto. *)
(*   destruct IHn. *)
(*   right; auto. *)
(*   left; auto. *)
(* Qed. *)

(* (* Definition run_interp : cfg -> option cfg := *) *)
(* (*   fix run_interp1 (c : cfg) : option cfg := ... *) *)
(* (*   with run_interp2 (c : cfg) : option cfg := ... *) *)
(* (*   with run_interp (c : cfg) : option cfg := ... *) *)
(* (*   for run_interp. *) *)

(* Definition run_interp := *)
(*   fix run_interp_a_1 (c : cfg_a) : {option cfg_a | ...} := ... *)
(*   with run_interp_a2 (c : cfg_a) : option cfg_a := ... *)
(*   with run_interp_b_1 (c : cfg_b) : option cfg_b := ... *)
(*   with run_interp_b_2 (c : cfg_b) : option cfg_b := ... *)
(*   with run_interp (c : {cfg_a}+{cfg_b}) : option ({cfg_a}+{cfg_b}) := ... *)
(*   for run_interp. *)


  
(* Definition run_interp := *)
(*   fix run_interp_a_1 (c : cfg_a) : option cfg_a := ... *)
(*   with run_interp_a2 (c : cfg_a) : option cfg_a := ... *)
(*   with run_interp_b_1 (c : cfg_b) : option cfg_b := ... *)
(*   with run_interp_b_2 (c : cfg_b) : option cfg_b := ... *)
(*   with run_interp (c : {cfg_a}+{cfg_b}) : option ({cfg_a}+{cfg_b}) := ... *)
(*   for run_interp. *)


Definition run_interp1 (c : cfg) : option cfg :=
  match c with
  | (vs, block ((break 0) :: rest)) => Some (vs, break 0)
  | _ => None
  end.

Definition run_interp2 (c : cfg) : option cfg :=
  match c with
  | (vs, block ((break 0) :: rest)) => Some (vs, block [])
  | _ => None
  end.

Definition run_interp3
           (c : cfg)
           (rec : forall (c' : cfg), MR lt measure_cfg c' c -> option cfg)
         : option cfg :=
  match c with
  | (vs, block stmts) =>
      match rec (vs, block stmts) (fill_here _ _) with
      | Some (vs', stmt') => Some (vs', block [stmt'])
      | None => None
      end
  | _ => None
  end.

Definition run_interp4
           (c : cfg)
           (rec : forall (c' : cfg), MR lt measure_cfg c' c -> option cfg)
         : option cfg :=
  match c with
  | (vs, block (s :: rest)) =>
      match rec (vs, block [s]) (fill_here _ _) with
      | Some (vs', block stmt') => Some (vs', block (stmt' ++ rest))
      | Some (vs', stmt') => Some (vs', block (stmt' :: rest))
      | None => None
      end
  | _ => None
  end.

Definition run_interp5 (c : cfg) : option cfg :=
  match c with
  | (vs, set n n') =>
      if Nat.ltb n (length vs) then
        Some (firstn n vs ++ [n'] ++ skipn (S n) vs, block [])%list
      else None
  | _ => None
  end.

Definition run_interp : cfg -> option cfg :=
  @Fix cfg (MR lt measure_cfg) measure_cfg_wf (fun _ => option cfg)
    (fun (c : cfg) (rec : forall (c' : cfg), MR lt measure_cfg c' c -> _) =>
      match run_interp1 c with
      | Some res => Some res
      | None =>
        match run_interp2 c with
        | Some res => Some res
        | None =>
          match run_interp3 c rec with
          | Some res => Some res
          | None =>
            match run_interp4 c rec with
            | Some res => Some res
            | None => run_interp5 c
            end
          end
        end
      end).

Check Fix.


(* Here's an even shorter definition of run_interp! *)
Definition mplus {A : Type} (o1 o2 : option A) : option A :=
  match o1 with
  | Some res => Some res
  | None => o2
  end.

Notation "o1 <|> o2" := (@mplus _ o1 o2) (at level 80, right associativity).

Definition run_interp' : cfg -> option cfg :=
  @Fix cfg (MR lt measure_cfg) measure_cfg_wf (fun _ => option cfg)
  (fun (c : cfg) (rec : forall (c' : cfg), MR lt measure_cfg c' c -> _) =>
    run_interp1 c <|> run_interp2 c <|> run_interp3 c rec <|> run_interp4 c rec <|> run_interp5 c).
