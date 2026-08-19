(** * TestCoinductiveTransparentSigma: Tests for animate_coinductive_transparent_sigma.
    Holes in the output are function-typed and wrapped in named inductive types
    (e.g. [zipStAn2Symb]) so that in the output it is clear which function each
    hole corresponds to.  coIndPush positions use [typeNmcoIndPushSymb] wrappers. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
Require Import Animation.HoleyResult.
Require Import Animation.coIndPreProcSigmaArrTp.
From Stdlib Require Import List.
From Stdlib Require Import Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.
Local Open Scope nat_scope.
Open Scope bs.

(* ------------------------------------------------------------------ *)

Module ImpSem.

Definition set (vs : nat -> nat) (v n : nat) : nat -> nat :=
  fun v' => if Nat.eqb v v' then n else vs v'.

Inductive exp : Type :=
| Const : nat -> exp
| Var   : nat -> exp
| Plus  : exp -> exp -> exp.

Fixpoint evalExp (vs : nat -> nat) (e : exp) : nat :=
  match e with
  | Const n     => n
  | Var v       => vs v
  | Plus e1 e2  => evalExp vs e1 + evalExp vs e2
  end.

Inductive cmd : Type :=
| Assign : nat -> exp -> cmd
| Seq    : cmd -> cmd -> cmd
| While  : exp -> cmd -> cmd.

CoInductive evalCmd : (nat -> nat) -> cmd -> (nat -> nat) -> Prop :=
| EvalAssign     : forall  vs v e,
     evalCmd vs (Assign v e) ((set vs v (evalExp vs e)))
| EvalSeq        : forall vs1 vs2 vs3 c1 c2,
    evalCmd vs1 c1 vs2 /\ evalCmd vs2 c2 vs3
    -> evalCmd vs1 (Seq c1 c2) vs3
| EvalWhileFalse : forall vs e c,
     evalExp vs e = 0
    -> evalCmd vs (While e c) vs
| EvalWhileTrue  : forall vs1' vs2' vs3' e c m,
     evalExp vs1' e = S m
    /\ evalCmd vs1' c vs2' /\ evalCmd vs2' (While e c) vs3'
    -> evalCmd vs1' (While e c) vs3'.

MetaRocq Run (animate_coinductive_with_fn_pos
  <? evalCmd ?> [("evalCmd", ([0;1], [2]))] 500).
 
Print fnType0.
Print cmd'.
Print nat'.  

End ImpSem.

Module bigStepTr.
Inductive ty : Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tvar : string -> tm
| tapp : tm -> tm -> tm
| tabs : string -> ty -> tm -> tm
| ttrue : tm
| tfalse : tm
| tif : tm -> tm -> tm -> tm.

Fixpoint eqFnty (tp : ty) (tp2 : ty) : bool :=
match tp with
| TBool => match tp2 with
           | TBool => true
           | _ => false
           end
| TArrow t1 t2  => match tp2 with
                     | TBool => false
                     | TArrow t1' t2'  => andb (eqFnty t1 t1') (eqFnty t2 t2')
                     end
end.

CoInductive coLst : Type :=
| coNil : coLst
| coSeq : tm -> coLst -> coLst.



Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tvar y => if String.eqb x y then s else t
  | tabs y T t1 => if String.eqb x y then t else tabs y T (subst x s t1)
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | ttrue => ttrue
  | tfalse => tfalse
  | tif t1 t2 t3 => tif (subst x s t1) (subst x s t2) (subst x s t3)

  end.

(* [step] is a standalone block; [bigStepTr] calls it from a separate block. *)

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall (z : string) (T : ty) (t w  : tm),
   step (tapp (tabs z T t) w) (subst z w t)
| ST_App1 : forall (t1 t1' t2 : tm),
    step t1 t1' ->
    step (tapp t1 t2) (tapp t1' t2)
| ST_IfTrue : forall (t1 t2 : tm),
    step (tif ttrue t1 t2) t1
| ST_IfFalse : forall (t1 t2 : tm),
    step (tif tfalse t1 t2) t2
| ST_If : forall (t1 t1' t2 t3 : tm),
    step t1 t1' ->
    step (tif t1 t2 t3) (tif t1' t2 t3)
| ST_Val1 : forall s, step (tvar s) (tvar s)
| ST_Val2 : forall v1 v2 v3, step (tabs v1 v2 v3) (tabs v1 v2 v3)
| ST_Val3 : step ttrue ttrue
| ST_Val4 : step tfalse tfalse.

CoInductive bigStepTr : tm -> coLst -> Prop :=
| bigVal1 : forall s, bigStepTr (tvar s) ((coSeq (tvar s)) coNil)
| bigVal2 : forall v1 v2 v3, bigStepTr (tabs v1 v2 v3) ((coSeq (tabs v1 v2 v3)) coNil)
| bigVal3 : bigStepTr ttrue ((coSeq ttrue) coNil)
| bigVal4 : bigStepTr tfalse ((coSeq tfalse) coNil)
| bigStep : forall t tr_lst t',
    step t t' /\ bigStepTr t' tr_lst -> bigStepTr t (coSeq t' tr_lst).
  
MetaRocq Run (animate_coinductive_with_fn_pos <? bigStepTr ?>
  [("bigStepTr", ([0], [1]));("step", ([0], [1]))] 500). 

Search (tm' -> tm' -> bool).

Print eqFncoLst'_1.
Print tm'.
Print coLst'.   
  
End bigStepTr.
Module StackStep.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.
(*
Fixpoint decEqsinstr : forall (t1 t2 : sinstr), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality. decide equality. decide equality. decide equality.
Defined.
*)
Definition eqFnsinstr (t1 t2 : sinstr) : bool :=
  true.

Definition stack := list nat.
Definition prog  := list sinstr.

Definition appSt (st : string -> nat) (s : string) : nat := st s.

Definition add (n1 n2 : nat) := n1 + n2.
Definition minus (n1 n2 : nat) := n1 - n2.
Definition mul (n1 n2 : nat) := n1 * n2.

Inductive stack_step : (string -> nat) -> list sinstr -> list nat -> list sinstr -> list nat -> Prop :=
| SS_Push  : forall st stk n p,
     stack_step st (SPush n :: p) stk p (n :: stk) 
| SS_Load  : forall st stk i p,
     
     stack_step (st) (SLoad i :: p)  stk p ((st i) :: stk) 
   
| SS_Plus  : forall st stk n m p, stack_step st (SPlus :: p) (n :: m :: stk) p ((add m  n) :: stk)
| SS_Minus : forall st stk n m p,
    stack_step st (SMinus :: p) (n :: m :: stk) p  ((minus m  n) :: stk)
| SS_Mult  : forall st stk n m p,
    stack_step st (SMult :: p) (n :: m :: stk) p  ((mul m  n) :: stk).
    
MetaRocq Run (animate_coinductive_with_fn_pos <? stack_step ?>
  [("stack_step", ([0;1;2], [3;4]))] 500 ).

Print fnType0.
Print nat'.  

Module zip.

CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.

CoFixpoint from (n : nat) : stream := Seq n (from (S n)).

CoInductive zipSt : stream -> stream -> stream -> Prop :=
| zip : forall n m s1 s2 s3 s4 s5 s6,
    s1 = Seq n s2 /\ s3 = Seq m s4 /\ zipSt s2 s4 s5 /\ s6 = Seq n (Seq m s5)
    -> zipSt s1 s3 s6.

MetaRocq Run (animate_coinductive_with_fn_pos <? zipSt ?>
  [("zipSt", ([0;1], [2]))] 100).
End zip.

Module integrateStreams.
(** A stream of naturals, with explicit undefined and nil sentinels. *)
Definition add (n1 n2 : nat) := n1 + n2.
CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.




CoFixpoint from (n : nat) : stream := Seq n (from (S n)).



(* ------------------------------------------------------------------ *)
(** ** Integrate *)

CoInductive Integrate : stream -> stream -> Prop :=
| integNil : Integrate nil nil
| integ : forall s2 s3 n s5, Integrate s2 s3 /\ addStm n s3 s5 -> Integrate (Seq n s2) (Seq n s5)

with addStm : nat -> stream -> stream -> Prop :=
| addStmNil : forall m, addStm m nil nil
| plusm : forall m s1 n s2, addStm m s1 s2 -> addStm m (Seq n s1) (Seq (add m n) s2).
MetaRocq Run (animate_coinductive_with_fn_pos <? Integrate ?>
  [("Integrate", ([0], [1])); ("addStm", ([0;1], [2]))] 100).
End integrateStreams.

(*
(** ** Chunk 1 unit tests: build_rel_context on evalCmd *)
MetaRocq Run (
  rc <- build_rel_context [("evalCmd", ([0;1], [2]))] ;;
  let '(rel_block_minds, modes_with_idx, rel_kns,
        ctor_eq_kns_raw, arg_kns_raw, ctor_eq_ind_apps_raw) := rc in
  v1 <- tmEval all (List.map snd rel_kns) ;;
  _ <- tmDefinition "brc_rel_kn_names" v1 ;;
  v2 <- tmEval all (List.map (fun mwi => List.length (snd mwi)) modes_with_idx) ;;
  _ <- tmDefinition "brc_idx_ctx_lens" v2 ;;
  v3 <- tmEval all (List.map snd ctor_eq_kns_raw) ;;
  _ <- tmDefinition "brc_ctor_eq_kn_names" v3 ;;
  v4 <- tmEval all (List.map snd arg_kns_raw) ;;
  _ <- tmDefinition "brc_arg_kn_names" v4 ;;
  v5 <- tmEval all (List.map (fun e => snd (fst e)) ctor_eq_ind_apps_raw) ;;
  _ <- tmDefinition "brc_ctor_eq_ind_app_names" v5 ;;
  tmReturn tt
).

Example brc_rel_kn_names_test :
  brc_rel_kn_names = ["evalCmd"] := eq_refl.
Example brc_idx_ctx_lens_test :
  brc_idx_ctx_lens = [3] := eq_refl.
Example brc_ctor_eq_kn_names_test :
  brc_ctor_eq_kn_names = ["nat"; "nat"] := eq_refl.
Example brc_arg_kn_names_test :
  brc_arg_kn_names = ["cmd"] := eq_refl.
Example brc_ctor_eq_ind_app_names_test :
  brc_ctor_eq_ind_app_names = [] := eq_refl.

(** ** Chunk 3 unit tests for evalCmd: collect_fn_app_infos *)
MetaRocq Run (
  rc <- build_rel_context [("evalCmd", ([0;1], [2]))] ;;
  let '(rel_block_minds, _, _, _, _, _) := rc in
  '(fai, fde, a2i, i2a, a2a) <- collect_fn_app_infos rel_block_minds [] ;;
  v1 <- tmEval all (List.map (fun e : fn_app_info => snd (fst (fst e))) fai) ;;
  _ <- tmDefinition "evalCmd_fai_fn_kn_idents" v1 ;;
  v2 <- tmEval all (List.length fde) ;;
  _ <- tmDefinition "evalCmd_fde_count" v2 ;;
  v3 <- tmEval all (List.map (fun e : a2i_edge => snd (snd e)) a2i) ;;
  _ <- tmDefinition "evalCmd_a2i_ind_idents" v3 ;;
  v4 <- tmEval all (List.map (fun e : i2a_edge => snd (fst e)) i2a) ;;
  _ <- tmDefinition "evalCmd_i2a_ind_idents" v4 ;;
  v5 <- tmEval all (List.length a2a) ;;
  _ <- tmDefinition "evalCmd_a2a_count" v5 ;;
  tmReturn tt
).

Example evalCmd_fai_fn_kn_idents_test :
  evalCmd_fai_fn_kn_idents = ["set"; "evalExp"] := eq_refl.
Example evalCmd_fde_count_test :
  evalCmd_fde_count = 0 := eq_refl.
Example evalCmd_a2i_ind_idents_test :
  evalCmd_a2i_ind_idents = ["nat"] := eq_refl.
Example evalCmd_i2a_ind_idents_test :
  evalCmd_i2a_ind_idents = ["nat"] := eq_refl.
Example evalCmd_a2a_count_test :
  evalCmd_a2a_count = 0 := eq_refl.

(** ** Chunk 3b unit tests for evalCmd: collect_all_lifting_edges *)
MetaRocq Run (
  rc <- build_rel_context [("evalCmd", ([0;1], [2]))] ;;
  let '(rel_block_minds, modes_with_idx, _, ctor_eq_kns_raw, arg_kns_raw, _) := rc in
  let seed_arrow_raw := lat_dedup_terms (flat_map lat_arrow_types_from_mwi modes_with_idx) in
  '(fai, fn_dep_edges, _, _, _) <- collect_fn_app_infos rel_block_minds [] ;;
  '(sii_i2i, sii_a2i, _, _) <- collect_all_lifting_edges arg_kns_raw ctor_eq_kns_raw seed_arrow_raw fai fn_dep_edges ;;
  v1 <- tmEval all (List.length sii_i2i) ;;
  _ <- tmDefinition "evalCmd_sii_count" v1 ;;
  v2 <- tmEval all (List.map (fun e : topo_edge => snd (fst e)) sii_i2i) ;;
  _ <- tmDefinition "evalCmd_sii_fst_idents" v2 ;;
  v3 <- tmEval all (List.map (fun e : topo_edge => snd (snd e)) sii_i2i) ;;
  _ <- tmDefinition "evalCmd_sii_snd_idents" v3 ;;
  v4 <- tmEval all (List.length sii_a2i) ;;
  _ <- tmDefinition "evalCmd_sii_a2i_count" v4 ;;
  tmReturn tt
).

Example evalCmd_sii_count_test :
  evalCmd_sii_count = 3 := eq_refl.
Example evalCmd_sii_fst_idents_test :
  evalCmd_sii_fst_idents = ["exp"; "nat"; "nat"] := eq_refl.
Example evalCmd_sii_snd_idents_test :
  evalCmd_sii_snd_idents = ["cmd"; "cmd"; "exp"] := eq_refl.
Example evalCmd_sii_a2i_count_test :
  evalCmd_sii_a2i_count = 1 := eq_refl.
*)

End StackStep.

(* ------------------------------------------------------------------ *)

(*
Module SpecPairsTest.

CoInductive relWithList : list nat -> list nat -> Prop :=
| rwl : forall l1 l2, relWithList l1 l2.

MetaRocq Run (
  rc <- build_rel_context [("relWithList", ([0], [1]))] ;;
  let '(_, modes_with_idx, _, _, _, ctor_eq_ind_apps_raw) := rc in
  sp <- declare_spec_pairs modes_with_idx ctor_eq_ind_apps_raw ;;
  v1 <- tmEval all (List.length sp) ;;
  _ <- tmDefinition "dsp_count" v1 ;;
  v2 <- tmEval all (List.map (fun p : spec_pair => snd (snd p)) sp) ;;
  _ <- tmDefinition "dsp_spec_kn_idents" v2 ;;
  v3 <- tmEval all (List.map (fun p : spec_pair => snd (fst (fst p))) sp) ;;
  _ <- tmDefinition "dsp_head_kn_idents" v3 ;;
  tmReturn tt
).

Example dsp_count_test :
  dsp_count = 1 := eq_refl.
Example dsp_spec_kn_idents_test :
  dsp_spec_kn_idents = ["listnat"] := eq_refl.
Example dsp_head_kn_idents_test :
  dsp_head_kn_idents = ["list"] := eq_refl.

End SpecPairsTest.
*)

(* ------------------------------------------------------------------ *)
(*
Module FnAppInfosTest.

Inductive myList : Type :=
| myNil  : myList
| myCons : nat -> myList -> myList.

Fixpoint myLen (l : myList) : nat :=
  match l with
  | myNil      => 0
  | myCons _ t => S (myLen t)
  end.

CoInductive lenRel : (list nat * nat) -> myList -> nat -> Prop :=
| lr_base : forall l p, lenRel p l (myLen l).
MetaRocq Run (ls <- collect_all_lifting_edges2
  [("lenRel", ([0;1], [2]))] 500 ;; ls' <- tmEval all ls ;; tmPrint ls').

(*
(** ** Chunk 3 unit tests: collect_fn_app_infos on lenRel *)
MetaRocq Run (
  rc <- build_rel_context [("lenRel", ([0], [1]))] ;;
  let '(rel_block_minds, _, _, _, _, _) := rc in
  '(fai, fde, a2i, i2a, a2a) <- collect_fn_app_infos rel_block_minds [] ;;
  v1 <- tmEval all (List.length fai) ;;
  _ <- tmDefinition "cfai_fn_count" v1 ;;
  v2 <- tmEval all (List.map (fun e : fn_app_info => snd (fst (fst e))) fai) ;;
  _ <- tmDefinition "cfai_fn_kn_idents" v2 ;;
  v3 <- tmEval all (List.length fde) ;;
  _ <- tmDefinition "cfai_edge_count" v3 ;;
  v4 <- tmEval all (List.map (fun e : topo_edge => snd (fst e)) fde) ;;
  _ <- tmDefinition "cfai_edge_in_kn_idents" v4 ;;
  v5 <- tmEval all (List.map (fun e : topo_edge => snd (snd e)) fde) ;;
  _ <- tmDefinition "cfai_edge_out_kn_idents" v5 ;;
  v6 <- tmEval all (List.length a2i) ;;
  _ <- tmDefinition "cfai_a2i_count" v6 ;;
  v7 <- tmEval all (List.length i2a) ;;
  _ <- tmDefinition "cfai_i2a_count" v7 ;;
  v8 <- tmEval all (List.length a2a) ;;
  _ <- tmDefinition "cfai_a2a_count" v8 ;;
  tmReturn tt
).

Example cfai_fn_count_test :
  cfai_fn_count = 1 := eq_refl.
Example cfai_fn_kn_idents_test :
  cfai_fn_kn_idents = ["myLen"] := eq_refl.
Example cfai_edge_count_test :
  cfai_edge_count = 1 := eq_refl.
Example cfai_edge_in_kn_idents_test :
  cfai_edge_in_kn_idents = ["myList"] := eq_refl.
Example cfai_edge_out_kn_idents_test :
  cfai_edge_out_kn_idents = ["nat"] := eq_refl.
Example cfai_a2i_count_test : cfai_a2i_count = 0 := eq_refl.
Example cfai_i2a_count_test : cfai_i2a_count = 0 := eq_refl.
Example cfai_a2a_count_test : cfai_a2a_count = 0 := eq_refl.

(** ** Chunk 3b: collect_all_lifting_edges on lenRel *)
MetaRocq Run (
  rc <- build_rel_context [("lenRel", ([0], [1]))] ;;
  let '(rel_block_minds, modes_with_idx, _, ctor_eq_kns_raw, arg_kns_raw, _) := rc in
  let seed_arrow_raw := lat_dedup_terms (flat_map lat_arrow_types_from_mwi modes_with_idx) in
  '(fai, fn_dep_edges, _, _, _) <- collect_fn_app_infos rel_block_minds [] ;;
  '(sii_i2i, sii_a2i, _, _) <- collect_all_lifting_edges arg_kns_raw ctor_eq_kns_raw seed_arrow_raw fai fn_dep_edges ;;
  v1 <- tmEval all (List.length sii_i2i) ;;
  _ <- tmDefinition "cfai_sii_count" v1 ;;
  v2 <- tmEval all (List.map (fun e : topo_edge => snd (fst e)) sii_i2i) ;;
  _ <- tmDefinition "cfai_sii_fst_idents" v2 ;;
  v3 <- tmEval all (List.map (fun e : topo_edge => snd (snd e)) sii_i2i) ;;
  _ <- tmDefinition "cfai_sii_snd_idents" v3 ;;
  v4 <- tmEval all (List.length sii_a2i) ;;
  _ <- tmDefinition "cfai_sii_a2i_count" v4 ;;
  tmReturn tt
).

Example cfai_sii_count_test : cfai_sii_count = 2 := eq_refl.
Example cfai_sii_fst_idents_test : cfai_sii_fst_idents = ["myList"; "nat"] := eq_refl.
Example cfai_sii_snd_idents_test : cfai_sii_snd_idents = ["nat"; "myList"] := eq_refl.
Example cfai_sii_a2i_count_test : cfai_sii_a2i_count = 0 := eq_refl.
*)

End FnAppInfosTest.
*)
