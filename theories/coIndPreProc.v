(** * coIndPreProc: Preprocessing for coinductive animation
    For each non-Prop type used as an argument type in any relation from the
    modes list, declare a lifted copy [T'] whose constructors are renamed with
    a prime suffix and an extra nullary [undefinedT] constructor is appended.
    Argument types are updated: if an old type was itself lifted, the lifted
    version is used; otherwise the original type is kept.  After running
    [preprocess_coind_types modes], the caller obtains an old-to-new kername
    mapping that can be passed to the animation engine. *)

Require Import Animation.AnimationResult.
Require Import Animation.AnimationTypes.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

From Stdlib Require Import List.
From Stdlib Require Import Streams.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.

Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.


(** A stream of naturals, with explicit undefined and nil sentinels. *)
CoInductive stream : Type :=
| nil : stream
| Seq : nat -> stream -> stream.



(* ------------------------------------------------------------------ *)
(** ** Integrate *)

CoInductive Integrate : stream -> stream -> Prop :=
| integNil : Integrate nil nil
| integ : forall s2 s3 n s5, Integrate s2 s3 /\ addStm n s3 s5 -> Integrate (Seq n s2) (Seq n s5)
with addStm : nat -> stream -> stream -> Prop :=
| addStmNil : forall m, addStm m nil nil
| plusm : forall m s1 n n' s2, addStm m s1 s2 /\ addNat m n n' -> addStm m (Seq n s1) (Seq (n') s2)
with
addNat : nat -> nat -> nat -> Prop :=
| addZero : forall n, addNat 0 n n
| addSucc : forall n m p, addNat n m p -> addNat (S n) m (S p).






Inductive isZero : bool -> nat -> Prop :=
| isT : isZero true 0
| isF : isZero false 1.

  
Inductive Len : list nat -> list nat -> nat -> Prop :=
| nilLen : forall l l' m, isZero true m /\ l = [] /\ l' = l -> Len l l' m
| ConsLen : forall l m x l', l' = l /\  Len l l' m -> Len (x::l) (x::l') (S m).
  

(*
MetaRocq Run (animate_coinductive Integrate <? Integrate ?>
  [("Integrate", ([0], [1])); ("addStm", ([0;1], [2])); ("addNat", ([0;1], [2])) ] 100).

*)


(* ================================================================== *)
(** ** Preprocessing: lift non-Prop argument types                    *)
(* ================================================================== *)

(** Collect all [kername]s that appear as the inductive name of a [tInd]
    node anywhere in a term. *)
Fixpoint collect_tind_kns (t : term) : list kername :=
  match t with
  | tInd ind _           => [inductive_mind ind]
  | tEvar _ args         => flat_map collect_tind_kns args
  | tCast c _ v          => collect_tind_kns c ++ collect_tind_kns v
  | tProd _ ty body
  | tLambda _ ty body    => collect_tind_kns ty ++ collect_tind_kns body
  | tLetIn _ val ty body =>
    collect_tind_kns val ++ collect_tind_kns ty ++ collect_tind_kns body
  | tApp f args          => collect_tind_kns f ++ flat_map collect_tind_kns args
  | tCase _ pred disc brs =>
    flat_map collect_tind_kns pred.(pparams) ++
    collect_tind_kns pred.(preturn) ++
    collect_tind_kns disc ++
    flat_map (fun br => collect_tind_kns br.(bbody)) brs
  | tProj _ c            => collect_tind_kns c
  | tFix   mfix _        =>
    flat_map (fun d => collect_tind_kns d.(dtype)) mfix ++
    flat_map (fun d => collect_tind_kns d.(dbody)) mfix
  | tCoFix mfix _        =>
    flat_map (fun d => collect_tind_kns d.(dtype)) mfix ++
    flat_map (fun d => collect_tind_kns d.(dbody)) mfix
  | _                    => []
  end.

(** Collect every [tApp (tInd head_kn _) [tInd arg1_kn _; ...]] in a term
    where ALL arguments are bare [tInd] nodes (no nested applications).
    Returns a list of [(head_kn, [arg_kn ...])] pairs (with duplicates).
    These are the parametric-type applications that can be monomorphised. *)
Fixpoint collect_ind_apps (t : term) : list (kername * list kername) :=
  let self_list ts := flat_map collect_ind_apps ts in
  match t with
  | tApp (tInd head _) args =>
    let all_tind :=
      forallb (fun a => match a with tInd _ _ => true | _ => false end) args in
    let arg_kns :=
      flat_map (fun a => match a with
                         | tInd ind _ => [inductive_mind ind]
                         | _          => []
                         end) args in
    let here := if all_tind then [(inductive_mind head, arg_kns)] else [] in
    here ++ self_list args
  | tApp f args          => collect_ind_apps f ++ self_list args
  | tInd _ _             => []
  | tEvar _ args         => self_list args
  | tCast c _ v          => collect_ind_apps c ++ collect_ind_apps v
  | tProd _ ty body
  | tLambda _ ty body    => collect_ind_apps ty ++ collect_ind_apps body
  | tLetIn _ val ty body =>
    collect_ind_apps val ++ collect_ind_apps ty ++ collect_ind_apps body
  | tCase _ pred disc brs =>
    flat_map collect_ind_apps pred.(pparams) ++
    collect_ind_apps pred.(preturn) ++
    collect_ind_apps disc ++
    flat_map (fun br => collect_ind_apps br.(bbody)) brs
  | tProj _ c            => collect_ind_apps c
  | tFix   mfix _        =>
    flat_map (fun d => collect_ind_apps d.(dtype)) mfix ++
    flat_map (fun d => collect_ind_apps d.(dbody)) mfix
  | tCoFix mfix _        =>
    flat_map (fun d => collect_ind_apps d.(dtype)) mfix ++
    flat_map (fun d => collect_ind_apps d.(dbody)) mfix
  | _                    => []
  end.

(** Deduplicate [(kername * list kername)] pairs by structural equality on the
    kername lists. Preserves first-occurrence order. *)
Definition dedup_ind_apps (l : list (kername * list kername))
    : list (kername * list kername) :=
  fold_left (fun acc p =>
    let match_entry q :=
      andb (eq_kername (fst q) (fst p))
           (andb (Nat.eqb #|snd q| #|snd p|)
                 (forallb (fun ab => eq_kername (fst ab) (snd ab))
                          (combine (snd q) (snd p)))) in
    if existsb match_entry acc then acc else List.app acc [p])
  l [].

(** After substituting concrete args for params in a constructor type,
    convert residual [tApp (tRel j) args] where [j] is a body self-ref at
    the current binder depth back to bare [tRel j].  The specialised type
    has no parameters, so these param-application shells are spurious.

    Body self-refs at binder depth [d]: [tRel d .. tRel (d+n_bodies-1)]. *)
Fixpoint strip_param_apps (n_bodies depth : nat) (t : term) : term :=
  match t with
  | tApp (tRel j) _ =>
    if andb (Nat.leb depth j) (Nat.ltb j (depth + n_bodies))
    then tRel j
    else t
  | tProd na ty body =>
    tProd na (strip_param_apps n_bodies depth ty)
             (strip_param_apps n_bodies (S depth) body)
  | tLambda na ty body =>
    tLambda na (strip_param_apps n_bodies depth ty)
               (strip_param_apps n_bodies (S depth) body)
  | tLetIn na val ty body =>
    tLetIn na (strip_param_apps n_bodies depth val)
              (strip_param_apps n_bodies depth ty)
              (strip_param_apps n_bodies (S depth) body)
  | tApp f args =>
    tApp (strip_param_apps n_bodies depth f)
         (List.map (strip_param_apps n_bodies depth) args)
  | _ => t
  end.

(** Strip [n] leading [tProd] binders from a type — used to remove the
    parameter foralls from [ind_type] when specialising a parametric type. *)
Fixpoint strip_leading_prods (n : nat) (t : term) : term :=
  match n, t with
  | S n', tProd _ _ body => strip_leading_prods n' body
  | _, _ => t
  end.

(** Replace every [tInd {mind=old_kn; ind=bidx} _] node with [tRel (depth+bidx)].
    This normalises constructor types from inductives that use [tInd] for
    self-references (instead of the [tRel] representation MetaRocq expects
    after removing params), eliminating universe-instance references like
    [list.u0] that would otherwise appear in the specialised body. *)
Fixpoint subst_self_ref (old_kn : kername) (depth : nat) (t : term) : term :=
  let r d := subst_self_ref old_kn d in
  match t with
  | tInd ind _ =>
    if eq_kername (inductive_mind ind) old_kn
    then tRel (depth + inductive_ind ind)
    else t
  | tApp f args     => tApp (r depth f) (List.map (r depth) args)
  | tProd na ty b   => tProd na (r depth ty) (r (S depth) b)
  | tLambda na ty b => tLambda na (r depth ty) (r (S depth) b)
  | tLetIn na v ty b => tLetIn na (r depth v) (r depth ty) (r (S depth) b)
  | tCast c k v     => tCast (r depth c) k (r depth v)
  | _               => t
  end.

(** Specialise a parametric mutual inductive [old_mind] at [concrete_args]
    (one term per parameter, in parameter order), producing a fresh
    monomorphic inductive body named [spec_name] with no remaining parameters.

    de Bruijn substitution convention (MetaRocq [subst l k t]):
    - [tRel i] with [i < k]         → unchanged
    - [tRel (k+j)] with [j < |l|]  → [lift k 0 l[j]]
    - [tRel i] with [i >= k+|l|]   → [tRel (i - |l|)]
    - binders increment [k] by 1 when entering body

    At depth 0 in [cstr_type]: [tRel 0..n_bodies-1] = body self-refs,
    [tRel n_bodies..n_bodies+n_params-1] = params.

    For [cstr_args] decl at snoc-index [snoc_i] (which has
    [n_args - 1 - snoc_i] outer arg binders already in scope):
      substitute at [k = n_bodies + (n_args - 1 - snoc_i)]. *)
Definition specialize_mind
    (old_mind      : mutual_inductive_body)
    (old_kn        : kername)
    (concrete_args : list term)
    (spec_name     : string)
    : mutual_inductive_body :=
  let n_bodies := #|old_mind.(ind_bodies)| in
  let n_params := #|old_mind.(ind_params)| in
  {| ind_finite    := old_mind.(ind_finite);
     ind_npars     := 0;
     ind_universes := Monomorphic_ctx;
     ind_variance  := None;
     ind_params    := [];
     ind_bodies    :=
       List.map (fun oib =>
         {| ind_name      := spec_name;
            ind_indices   := oib.(ind_indices);
            ind_sort      := Sort.type0;
            ind_type      := tSort Sort.type0;
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              List.map (fun c =>
                let n_args   := #|c.(cstr_args)| in
                let new_args :=
                  mapi (fun snoc_i d =>
                    let outer := n_args - 1 - snoc_i in
                    (* cstr_args.decl_type has params as free vars at tRel(n_bodies+j+outer).
                       Normalise tInd self-refs first, then substitute params at k=n_bodies+outer. *)
                    let d0 := subst_self_ref old_kn outer d.(decl_type) in
                    let t0 := subst concrete_args (n_bodies + outer) d0 in
                    let t1 := strip_param_apps n_bodies outer t0 in
                    {| decl_name := d.(decl_name);
                       decl_body := None;
                       decl_type := t1 |})
                  c.(cstr_args) in
                (* cstr_type has params as bound tProd binders (not free vars).
                   Strip param binders first so params become free at tRel 0..n_params-1,
                   then substitute at k=0. Body self-refs shift from tRel n_params..
                   to tRel 0.. automatically via subst. *)
                let ct0 := subst_self_ref old_kn 0 c.(cstr_type) in
                let ct1 := strip_leading_prods n_params ct0 in
                let t0  := subst concrete_args 0 ct1 in
                let t1  := strip_param_apps n_bodies 0 t0 in
                {| cstr_name    := spec_name ++ "_" ++ c.(cstr_name);
                   cstr_args    := new_args;
                   cstr_indices := c.(cstr_indices);
                   cstr_type    := t1;
                   cstr_arity   := c.(cstr_arity) |})
              oib.(ind_ctors);
            ind_projs     := [];
            ind_relevance := oib.(ind_relevance) |})
       old_mind.(ind_bodies) |}.

(** True iff the first [one_inductive_body] of [mind] lives in Prop or SProp.
    We check [ind_sort] (type [Sort.t]) directly, since singleton Props
    (e.g. [and], [True]) have [ind_kelim = IntoAny] despite being in Prop. *)
Definition is_prop_mind (mind : mutual_inductive_body) : bool :=
  match mind.(ind_bodies) with
  | []        => false
  | oib :: _ =>
    match oib.(ind_sort) with
    | sProp | sSProp => true
    | _              => false
    end
  end.

(** Substitute every [tInd kn _] node according to
    [mapping : list (old_kn * new_ind)] where [new_ind] carries both the new
    [inductive_mind] and the [inductive_ind] within its (possibly mutual) block.
    For single-body inductives [inductive_ind = 0] in both old and new, so the
    semantics are identical to the previous [kername]-only mapping. *)
Fixpoint subst_ind_kns (mapping : list (kername * inductive)) (t : term) : term :=
  let lookup ind :=
    match find (fun p => eq_kername (fst p) (inductive_mind ind)) mapping with
    | Some (_, ind') => ind'
    | None           => ind
    end in
  match t with
  | tInd ind univs =>
    tInd (lookup ind) univs
  | tEvar n args   => tEvar n (List.map (subst_ind_kns mapping) args)
  | tCast c k v    => tCast (subst_ind_kns mapping c) k (subst_ind_kns mapping v)
  | tProd na ty body =>
    tProd na (subst_ind_kns mapping ty) (subst_ind_kns mapping body)
  | tLambda na ty body =>
    tLambda na (subst_ind_kns mapping ty) (subst_ind_kns mapping body)
  | tLetIn na val ty body =>
    tLetIn na (subst_ind_kns mapping val)
              (subst_ind_kns mapping ty)
              (subst_ind_kns mapping body)
  | tApp f args =>
    tApp (subst_ind_kns mapping f) (List.map (subst_ind_kns mapping) args)
  | tCase ci pred disc brs =>
    let ci' :=
      {| ci_ind      := lookup ci.(ci_ind);
         ci_npar      := ci.(ci_npar);
         ci_relevance := ci.(ci_relevance) |} in
    let pred' :=
      {| pparams  := List.map (subst_ind_kns mapping) pred.(pparams);
         puinst   := pred.(puinst);
         pcontext := pred.(pcontext);
         preturn  := subst_ind_kns mapping pred.(preturn) |} in
    tCase ci' pred' (subst_ind_kns mapping disc)
      (List.map (fun br => {| bcontext := br.(bcontext);
                              bbody    := subst_ind_kns mapping br.(bbody) |}) brs)
  | tProj p c => tProj p (subst_ind_kns mapping c)
  | tFix mfix idx =>
    tFix (List.map (fun d => {| dname := d.(dname);
                                dtype := subst_ind_kns mapping d.(dtype);
                                dbody := subst_ind_kns mapping d.(dbody);
                                rarg  := d.(rarg) |}) mfix) idx
  | tCoFix mfix idx =>
    tCoFix (List.map (fun d => {| dname := d.(dname);
                                  dtype := subst_ind_kns mapping d.(dtype);
                                  dbody := subst_ind_kns mapping d.(dbody);
                                  rarg  := d.(rarg) |}) mfix) idx
  | _ => t
  end.

Definition subst_ind_kns_decl (mapping : list (kername * inductive))
    (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map (subst_ind_kns mapping) d.(decl_body);
     decl_type := subst_ind_kns mapping d.(decl_type) |}.

(** Look up [tApp (tInd head_kn _) [tInd arg_kn1 _; ...]] in a mapping whose
    values are [kername] (used for [spec_unlifted_kn_map]). *)
Definition lookup_app_kn
    (app_kn_mapping : list (kername * list kername * kername))
    (f : term) (args : list term) : option kername :=
  match f with
  | tInd head _ =>
    let head_kn := inductive_mind head in
    if forallb (fun a => match a with tInd _ _ => true | _ => false end) args then
      let arg_kns :=
        flat_map (fun a =>
          match a with tInd ind _ => [inductive_mind ind] | _ => [] end) args in
      match find (fun e =>
        andb (eq_kername (fst (fst e)) head_kn)
             (andb (Nat.eqb #|snd (fst e)| #|arg_kns|)
                   (forallb (fun ab => eq_kername (fst ab) (snd ab))
                            (combine (snd (fst e)) arg_kns))))
        app_kn_mapping with
      | Some e => Some (snd e)
      | None   => None
      end
    else None
  | _ => None
  end.

(** Look up [tApp (tInd head_kn _) [tInd arg_kn1 _; ...]] in a mapping whose
    values are [inductive] (used for [app_kn_mapping] after mutual-block lifting).
    Returns [Some lifted_ind] where [lifted_ind] carries both the block kname and
    the correct body index within that block. *)
Definition lookup_app_kn_ind
    (app_kn_mapping : list (kername * list kername * inductive))
    (f : term) (args : list term) : option inductive :=
  match f with
  | tInd head _ =>
    let head_kn := inductive_mind head in
    if forallb (fun a => match a with tInd _ _ => true | _ => false end) args then
      let arg_kns :=
        flat_map (fun a =>
          match a with tInd ind _ => [inductive_mind ind] | _ => [] end) args in
      match find (fun e =>
        andb (eq_kername (fst (fst e)) head_kn)
             (andb (Nat.eqb #|snd (fst e)| #|arg_kns|)
                   (forallb (fun ab => eq_kername (fst ab) (snd ab))
                            (combine (snd (fst e)) arg_kns))))
        app_kn_mapping with
      | Some e => Some (snd e)
      | None   => None
      end
    else None
  | _ => None
  end.

(** Substitute a term from a relation's [ind_indices] for use as a constructor
    argument type in a new constructor being added to a lifted type.

    Three cases apply:
    - [tApp (tInd head_kn) [tInd arg_kns...]] matching [app_kn_mapping]
      → [tInd lifted_spec_kn []]  (whole application replaced by monomorphic type)
    - [self_old_kn] → [tRel (self_base + depth)]  (self-reference via tRel)
    - other kns in [ext_mapping] → [tInd new_kn]  (already declared)

    [depth] counts binders above the current subterm and is incremented under
    [tProd]/[tLambda]/[tLetIn] so that self-reference indices shift correctly. *)
Fixpoint subst_idx_type
    (self_old_kn          : kername)
    (self_base            : nat)
    (ext_mapping          : list (kername * inductive))
    (app_kn_mapping       : list (kername * list kername * inductive))
    (spec_unlifted_kn_map : list ((kername * list kername) * kername))
    (depth                : nat)
    (t                    : term) : term :=
  let r d := subst_idx_type self_old_kn self_base ext_mapping
               app_kn_mapping spec_unlifted_kn_map d in
  match t with
  | tInd ind univs =>
    let kn := inductive_mind ind in
    if eq_kername kn self_old_kn
    then tRel (self_base + depth)
    else match find (fun p => eq_kername (fst p) kn) ext_mapping with
         | Some (_, new_ind) => tInd new_ind univs
         | None => t
         end
  | tApp f args =>
    (* Specialised parametric self-reference: e.g. [list nat] when
       self_old_kn = listnat_kn and (list,[nat])→listnat in the spec map. *)
    match lookup_app_kn spec_unlifted_kn_map f args with
    | Some spec_kn =>
      if eq_kername spec_kn self_old_kn
      then tRel (self_base + depth)
      else
        match lookup_app_kn_ind app_kn_mapping f args with
        | Some lifted_ind =>
          if eq_kername (inductive_mind lifted_ind) self_old_kn
          then tRel (self_base + depth)
          else tInd lifted_ind []
        | None => tApp (r depth f) (List.map (r depth) args)
        end
    | None =>
      match lookup_app_kn_ind app_kn_mapping f args with
      | Some lifted_ind =>
        if eq_kername (inductive_mind lifted_ind) self_old_kn
        then tRel (self_base + depth)
        else tInd lifted_ind []
      | None => tApp (r depth f) (List.map (r depth) args)
      end
    end
  | tProd na ty b   => tProd na (r depth ty) (r (S depth) b)
  | tLambda na ty b => tLambda na (r depth ty) (r (S depth) b)
  | tLetIn na v ty b => tLetIn na (r depth v) (r depth ty) (r (S depth) b)
  | tCast c k v     => tCast (r depth c) k (r depth v)
  | _               => t
  end.

(** For the [body_idx]-th body of the lifted mutual block (having [n_bodies]
    bodies and parameter context [params']), compute the extra constructors
    derived from the relation modes.

    For each mode entry [(rel_nm, (in_pos, out_pos), idx_ctx)]:
    - [idx_ctx] is the [ind_indices] of that relation body (outer-to-inner).
    - For each output position [op] whose type contains [old_kn], add:
        [rel_nm ++ "An" ++ string_of_nat op : <lifted inputs> -> T']
      where the lifted input types come from [idx_ctx[ip]] for [ip] in [in_pos],
      with self-references replaced by the appropriate [tRel] index. *)
Definition compute_extra_cstrs
    (old_kn                 : kername)
    (body_idx               : nat)
    (n_bodies               : nat)
    (cparams                : context)
    (full_mapping           : list (kername * inductive))
    (app_kn_mapping         : list (kername * list kername * inductive))
    (spec_unlifted_kn_map   : list ((kername * list kername) * kername))
    (modes_with_idx         : list ((string * (list nat * list nat)) * list context_decl))
    : list constructor_body :=
  let n_params  := #|cparams| in
  let self_base := n_params + n_bodies - 1 - body_idx in
  let ext       := filter (fun p => negb (eq_kername (fst p) old_kn)) full_mapping in
  flat_map (fun mwi =>
    let nm      := fst (fst mwi) in
    let in_pos  := fst (snd (fst mwi)) in
    let out_pos := snd (snd (fst mwi)) in
    let idx_ctx := snd mwi in
    (* ind_indices uses snoc order: last (innermost) arg is at list index 0.
       Mode positions are argument-order (0 = first/leftmost). Convert:
         snoc_idx = #|idx_ctx| - 1 - arg_pos *)
    let n_idx := #|idx_ctx| in
    flat_map (fun op =>
      let snoc_op := n_idx - 1 - op in
      match nth_error idx_ctx snoc_op with
      | None => []
      | Some od =>
        (* Only add an extra constructor when [old_kn] is the ROOT of the
           output type, not merely a type argument.
           Also recognise specialised parametric applications: e.g.
           [list nat] at an output position belongs to [listnat], not [list]. *)
        let root_matches :=
          match od.(decl_type) with
          | tInd ind _  => eq_kername (inductive_mind ind) old_kn
          | tApp f args =>
            (* Check spec_unlifted_kn_map FIRST: it maps the original parametric
               application (e.g. [list nat]) to the unlifted specialised kname
               (e.g. [listnat_kn]).  This correctly identifies the output type
               regardless of whether the lifted version lives in a standalone or
               combined mutual block.  [app_kn_mapping] stores the *lifted*
               inductive, whose [inductive_mind] may differ from [old_kn] when
               the type is part of a combined block (e.g. listnat' at ind=1 in
               the "nat'" block) — checking it against [old_kn] would give a
               false negative in that case. *)
            match lookup_app_kn spec_unlifted_kn_map f args with
            | Some spec_kn => eq_kername spec_kn old_kn
            | None =>
              match lookup_app_kn_ind app_kn_mapping f args with
              | Some lifted_ind => eq_kername (inductive_mind lifted_ind) old_kn
              | None =>
                match f with
                | tInd ind _ => eq_kername (inductive_mind ind) old_kn
                | _          => false
                end
              end
            end
          | _ => false
          end in
        if root_matches
        then
          (* Build arg decls in outermost-first order, then reverse to snoc
             order (innermost-first) as required by MetaRocq's context and
             it_mkProd_or_LetIn conventions. *)
          let input_decls :=
            List.rev (snd (fold_left (fun da ip =>
              let depth := fst da in
              let acc   := snd da in
              let snoc_ip := n_idx - 1 - ip in
              match nth_error idx_ctx snoc_ip with
              | None => (S depth, acc)
              | Some d =>
                let t := subst_idx_type old_kn self_base ext app_kn_mapping
                           spec_unlifted_kn_map depth d.(decl_type) in
                (S depth, List.app acc
                   [{| decl_name := d.(decl_name);
                       decl_body := None;
                       decl_type := t |}])
              end)
            in_pos (0, []))) in
          let n_args  := #|input_decls| in
          let rel_idx := n_params + n_args + n_bodies - 1 - body_idx in
          let return_t :=
            if Nat.eqb n_params 0 then tRel rel_idx
            else tApp (tRel rel_idx)
                      (List.map tRel (rev (seq n_args n_params))) in
          [{| cstr_name    := nm ++ "An" ++ string_of_nat op;
              cstr_args    := input_decls;
              cstr_indices := [];
              cstr_type    := it_mkProd_or_LetIn (List.app cparams input_decls) return_t;
              cstr_arity   := n_args |}]
        else []
      end)
    out_pos)
  modes_with_idx.

(** [mind_body_to_entry] in MetaRocq 1.4 hardcodes [mind_entry_finite := Finite],
    discarding the [ind_finite] field.  We wrap it to override that one field so
    that a CoInductive source yields a CoInductive lifted copy. *)
Definition tmMkInductivePreserveFinite (mind : mutual_inductive_body)
    : TemplateMonad unit :=
  let entry  := mind_body_to_entry mind in
  let entry' :=
    {| mind_entry_record    := entry.(mind_entry_record);
       mind_entry_finite    := mind.(ind_finite);
       mind_entry_params    := entry.(mind_entry_params);
       mind_entry_inds      := entry.(mind_entry_inds);
       mind_entry_universes := entry.(mind_entry_universes);
       mind_entry_template  := entry.(mind_entry_template);
       mind_entry_variance  := entry.(mind_entry_variance);
       mind_entry_private   := entry.(mind_entry_private) |} in
  tmMkInductive false entry'.

(** Replace every [tInd {mind=block_kn; ind=j} _] node with the de Bruijn
    variable for the j-th body of the mutual block at the given binder
    depth.  In a mutual block of [n] bodies, body j is at
    [tRel (depth + n - 1 - j)] when no constructor arguments have been
    bound yet (depth = 0); depth increases by 1 for each [tProd] binder.

    This is needed because during [tmMkInductive] the block itself is not
    yet in the environment, so any intra-block cross-body reference MUST
    use [tRel], not [tInd]. *)
Fixpoint subst_block_inds_to_rels
    (block_kn : kername) (n_bodies depth : nat) (t : term) : term :=
  let r d := subst_block_inds_to_rels block_kn n_bodies d in
  match t with
  | tInd ind univs =>
    if eq_kername (inductive_mind ind) block_kn
    then tRel (depth + n_bodies - 1 - inductive_ind ind)
    else t
  | tEvar ev args    => tEvar ev (List.map (r depth) args)
  | tCast c kind ty  => tCast (r depth c) kind (r depth ty)
  | tProd  na ty b   => tProd  na (r depth ty) (r (S depth) b)
  | tLambda na ty b  => tLambda na (r depth ty) (r (S depth) b)
  | tLetIn na v ty b => tLetIn na (r depth v) (r depth ty) (r (S depth) b)
  | tApp f args      => tApp (r depth f) (List.map (r depth) args)
  | tProj p c        => tProj p (r depth c)
  | _                => t
  end.

(** Shift all de Bruijn variables at positions ≥ k by n in a term.
    Used to adjust self-reference [tRel] indices when embedding a standalone
    inductive body into a larger mutual block position. *)
Fixpoint lift_term (n k : nat) (t : term) : term :=
  let lk  := lift_term n k     in
  let lk1 := lift_term n (S k) in
  match t with
  | tRel i           => tRel (if Nat.leb k i then i + n else i)
  | tEvar ev args    => tEvar ev (List.map lk args)
  | tCast c kind ty  => tCast (lk c) kind (lk ty)
  | tProd  na ty b   => tProd  na (lk ty) (lk1 b)
  | tLambda na ty b  => tLambda na (lk ty) (lk1 b)
  | tLetIn na v ty b => tLetIn na (lk v) (lk ty) (lk1 b)
  | tApp f args      => tApp (lk f) (List.map lk args)
  | tProj p c        => tProj p (lk c)
  | tFix   mfix idx  =>
    let m := #|mfix| in
    tFix (List.map (fun d =>
      {| dname := d.(dname); dtype := lk d.(dtype);
         dbody := lift_term n (k + m) d.(dbody); rarg := d.(rarg) |}) mfix) idx
  | tCoFix mfix idx  =>
    let m := #|mfix| in
    tCoFix (List.map (fun d =>
      {| dname := d.(dname); dtype := lk d.(dtype);
         dbody := lift_term n (k + m) d.(dbody); rarg := d.(rarg) |}) mfix) idx
  | _                => t
  end.

Definition lift_decl (n k : nat) (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map (lift_term n k) d.(decl_body);
     decl_type := lift_term n k d.(decl_type) |}.

(** Produce the lifted [mutual_inductive_body] for [old_kn] → [new_kn].
    [ext_mapping] maps all OTHER old types to their new counterparts.
    [modes_with_idx] provides the relation mode info and [ind_indices] contexts
    used to generate extra constructors (one per relation output position that
    targets this type). *)
Polymorphic Definition make_lifted_mind
    (old_mind             : mutual_inductive_body)
    (old_kn               : kername)
    (new_ind              : inductive)
    (ext_mapping          : list (kername * inductive))
    (app_kn_mapping       : list (kername * list kername * inductive))
    (spec_unlifted_kn_map : list ((kername * list kername) * kername))
    (modes_with_idx       : list ((string * (list nat * list nat)) * list context_decl))
    (block_n_bodies       : nat)
    (block_body_offset    : nat)
    : mutual_inductive_body :=
  let full          := (old_kn, new_ind) :: ext_mapping in
  let params'       := List.map (subst_ind_kns_decl full) old_mind.(ind_params) in
  (* The block kname is the mind of new_ind — all bodies share it. *)
  let block_kn_mind := inductive_mind new_ind in
  (* Step 3 helpers: replace tInd {mind=block_kn_mind; ind=j} with
     tRel(depth + block_n_bodies - 1 - j).  This is necessary because
     cross-body references within the mutual block must use tRel during
     tmMkInductive (the block is not yet in the environment at that point). *)
  let s3t depth t  := subst_block_inds_to_rels block_kn_mind block_n_bodies depth t in
  let s3d depth d  :=
    {| decl_name := d.(decl_name);
       decl_body := option_map (s3t depth) d.(decl_body);
       decl_type := s3t depth d.(decl_type) |} in
  (* Apply s3d to each snoc[i] with depth = #|args| - 1 - i. *)
  let s3args args  :=
    let n_a := #|args| in
    mapi (fun snoc_i d => s3d (n_a - 1 - snoc_i) d) args in
  {| ind_finite    := old_mind.(ind_finite);
     ind_npars     := old_mind.(ind_npars);
     ind_universes := old_mind.(ind_universes);
     ind_variance  := old_mind.(ind_variance);
     ind_params    := params';
     ind_bodies    :=
       mapi (fun i oib =>
         let block_body_idx := block_body_offset + i in
         (* delta = how many extra bodies sit above this one's self-ref slot
            in the new combined block vs. the original standalone block.
            Standalone self-ref = tRel n_params; new self-ref = tRel (n_params + delta). *)
         let delta  := block_n_bodies - 1 - block_body_idx in
         let n_par  := #|params'| in
         let extra := compute_extra_cstrs old_kn block_body_idx block_n_bodies params' full
                        app_kn_mapping spec_unlifted_kn_map modes_with_idx in
         {| ind_name      := oib.(ind_name) ++ "'";
            ind_indices   := List.map (subst_ind_kns_decl full) oib.(ind_indices);
            ind_sort      := oib.(ind_sort);
            ind_type      := subst_ind_kns full oib.(ind_type);
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              (* Original constructors: step1 (subst knames) + step2 (lift tRels)
                 + step3 (cross-body tInd → tRel). *)
              List.map (fun c =>
                let args1 := List.map (subst_ind_kns_decl full) c.(cstr_args) in
                let args2 := List.map (lift_decl delta n_par) args1 in
                {| cstr_name    := c.(cstr_name) ++ "'";
                   cstr_args    := s3args args2;
                   cstr_indices := List.map (s3t 0)
                                     (List.map (lift_term delta n_par)
                                       (List.map (subst_ind_kns full) c.(cstr_indices)));
                   cstr_type    := s3t 0
                                     (lift_term delta n_par
                                       (subst_ind_kns full c.(cstr_type)));
                   cstr_arity   := c.(cstr_arity) |})
              oib.(ind_ctors)
              (* Extra constructors already use correct tRel for self and
                 tInd {block_kn_mind, j} for cross-body — apply step3 only. *)
              ++ List.map (fun c =>
                {| cstr_name    := c.(cstr_name);
                   cstr_args    := s3args c.(cstr_args);
                   cstr_indices := List.map (s3t 0) c.(cstr_indices);
                   cstr_type    := s3t 0 c.(cstr_type);
                   cstr_arity   := c.(cstr_arity) |})
              extra;
            ind_projs     := oib.(ind_projs);
            ind_relevance := oib.(ind_relevance) |})
       old_mind.(ind_bodies) |}.

(** Deduplicate a list of kernames preserving first-occurrence order. *)
Definition dedup_kns (kns : list kername) : list kername :=
  fold_left (fun acc kn =>
    if existsb (eq_kername kn) acc then acc else List.app acc [kn])
  kns [].

(** Kernames in [mapping] that appear as arg types of [mind]'s constructors,
    excluding [self_kn] (self-references are not cross-dependencies). *)
Definition direct_deps_in_mapping
    (self_kn : kername)
    (mind    : mutual_inductive_body)
    (mapping : list (kername * kername))
    : list kername :=
  let arg_kns :=
    flat_map (fun oib =>
      flat_map (fun c =>
        flat_map (fun d => collect_tind_kns d.(decl_type)) c.(cstr_args))
      oib.(ind_ctors))
    mind.(ind_bodies) in
  dedup_kns
    (filter (fun kn =>
       andb (negb (eq_kername kn self_kn))
            (existsb (fun p => eq_kername kn (fst p)) mapping))
    arg_kns).

(** Kahn's topological sort: returns [type_kns] reordered so that every
    type comes after all the other types in [mapping] that it depends on.
    [minds_assoc] is [(kn, mutual_inductive_body)] for each kn in [type_kns].
    [extra_deps] is a list of [(a, b)] meaning [a] must come after [b].
    These are mode-derived deps: output types must come after their input types
    so that extra constructors can reference already-declared lifted inputs.
    [fuel] bounds the number of passes (len + 1 is always sufficient for DAGs). *)
Fixpoint topo_sort_kns
    (remaining   : list kername)
    (minds_assoc : list (kername * mutual_inductive_body))
    (mapping     : list (kername * kername))
    (extra_deps  : list (kername * kername))
    (done        : list kername)
    (fuel        : nat)
    : list kername :=
  match fuel with
  | 0 => List.app done remaining
  | S fuel =>
    match remaining with
    | [] => done
    | _  =>
      let deps_of kn :=
        let struct_deps :=
          match find (fun p => eq_kername (fst p) kn) minds_assoc with
          | Some (_, mind) => direct_deps_in_mapping kn mind mapping
          | None           => []
          end in
        let mode_deps :=
          List.map snd (filter (fun p => eq_kername (fst p) kn) extra_deps) in
        dedup_kns (List.app struct_deps mode_deps) in
      let is_ready kn := forallb (fun dep => existsb (eq_kername dep) done) (deps_of kn) in
      let ready     := filter is_ready remaining in
      let not_ready := filter (fun kn => negb (is_ready kn)) remaining in
      match ready with
      | [] => List.app done remaining  (* cycle: append rest as-is *)
      | _  => topo_sort_kns not_ready minds_assoc mapping extra_deps (List.app done ready) fuel
      end
    end
  end.

(** Collect all [tInd] knames from a [mutual_inductive_body]'s bodies. *)
Definition collect_kns_from_mind (m : mutual_inductive_body) : list kername :=
  dedup_kns (flat_map (fun oib =>
    List.app
      (flat_map (fun c =>
        List.app (flat_map (fun d => collect_tind_kns d.(decl_type)) c.(cstr_args))
        (List.app (flat_map collect_tind_kns c.(cstr_indices))
                  (collect_tind_kns c.(cstr_type))))
      oib.(ind_ctors))
      (List.app (flat_map (fun d => collect_tind_kns d.(decl_type)) oib.(ind_indices))
                (collect_tind_kns oib.(ind_type))))
  m.(ind_bodies)).

(** Merge the groups containing [kn1] and [kn2] in a union-find represented
    as a list of groups. No-op if they are already in the same group. *)
Definition uf_merge (kn1 kn2 : kername) (groups : list (list kername))
    : list (list kername) :=
  let g1_opt := find (fun g => existsb (eq_kername kn1) g) groups in
  let g2_opt := find (fun g => existsb (eq_kername kn2) g) groups in
  match g1_opt, g2_opt with
  | Some grp1, Some grp2 =>
    if existsb (eq_kername kn1) grp2 then groups
    else
      let merged := dedup_kns (grp1 ++ grp2) in
      let rest   :=
        filter (fun g =>
          andb (negb (existsb (eq_kername kn1) g))
               (negb (existsb (eq_kername kn2) g))) groups in
      merged :: rest
  | _, _ => groups
  end.

(** Partition [kns] into connected components given undirected [edges]. *)
Definition group_connected_components
    (kns   : list kername)
    (edges : list (kername * kername))
    : list (list kername) :=
  let singletons := List.map (fun kn => [kn]) kns in
  fold_left (fun gs e => uf_merge (fst e) (snd e) gs) edges singletons.

(** Apply a kname→inductive remap to every term in a [mutual_inductive_body]. *)
Definition remap_mind_kns
    (remap : list (kername * inductive))
    (m     : mutual_inductive_body)
    : mutual_inductive_body :=
  {| ind_finite    := m.(ind_finite);
     ind_npars     := m.(ind_npars);
     ind_universes := m.(ind_universes);
     ind_variance  := m.(ind_variance);
     ind_params    := List.map (subst_ind_kns_decl remap) m.(ind_params);
     ind_bodies    :=
       List.map (fun oib =>
         {| ind_name      := oib.(ind_name);
            ind_indices   := List.map (subst_ind_kns_decl remap) oib.(ind_indices);
            ind_sort      := oib.(ind_sort);
            ind_type      := subst_ind_kns remap oib.(ind_type);
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              List.map (fun c =>
                {| cstr_name    := c.(cstr_name);
                   cstr_args    := List.map (subst_ind_kns_decl remap) c.(cstr_args);
                   cstr_indices := List.map (subst_ind_kns remap) c.(cstr_indices);
                   cstr_type    := subst_ind_kns remap c.(cstr_type);
                   cstr_arity   := c.(cstr_arity) |})
              oib.(ind_ctors);
            ind_projs     := oib.(ind_projs);
            ind_relevance := oib.(ind_relevance) |})
       m.(ind_bodies) |}.

(** Given a [mode_map], find all non-Prop types occurring as argument types
    of the listed relations, declare lifted copies, and return:
    - [type_mapping]   : old kname → new kname for each lifted data type
    - [app_kn_mapping] : (head_kn, [arg_kns], lifted_spec_kn) for each
      parametric application (e.g. [list nat]) that was monomorphised to a
      fresh inductive (e.g. [listnat']) before lifting.

    Parametric-type applications found in index types are specialised first
    (Step 4b) and then lifted by the same pipeline as monomorphic types. *)
Polymorphic Definition preprocess_coind_types
    (modes : mode_map)
    : TemplateMonad (list (kername * inductive) * list (kername * list kername * inductive)) :=
  (* Step 1: resolve each mode entry to a specific body (kn + body index) *)
  rel_inds <- monad_map (fun p =>
    let nm := fst p in
    refs <- tmLocate nm ;;
    match find (fun g =>
      match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("preprocess_coind_types: cannot locate '" ++ nm ++ "'")
    end)
  modes ;;
  (* Step 2: quote each distinct mutual block once *)
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;;
    tmReturn (kn, mind))
    rel_block_kns ;;
  (* Step 3: build modes_with_idx — pair each mode entry with the ind_indices
     of the specific relation body it names *)
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let nm      := fst mode_e in
      let in_out  := snd mode_e in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None     => []
          | Some oib => oib.(ind_indices)
          end
        end in
      ((nm, in_out), idx_ctx))
    (combine modes rel_inds) in
  let rel_kns := dedup_kns (List.map inductive_mind rel_inds) in
  (* Step 4: collect all tInd knames from every index-type decl *)
  let arg_kns_raw :=
    flat_map (fun mwi =>
      let in_pos  := fst (snd (fst mwi)) in
      let out_pos := snd (snd (fst mwi)) in
      let idx_ctx := snd mwi in
      flat_map (fun i =>
        match nth_error idx_ctx i with
        | Some d => collect_tind_kns d.(decl_type)
        | None   => []
        end)
      (List.app in_pos out_pos))
    modes_with_idx in
  let arg_kns :=
    dedup_kns (filter (fun kn => negb (existsb (eq_kername kn) rel_kns)) arg_kns_raw) in
  cur_mp <- tmCurrentModPath tt ;;
  (* Step 4b: detect parametric-type applications in every index-type decl
     and create a fresh monomorphic specialisation for each unique one.
     E.g. [list nat] → fresh inductive [listnat] (npars = 0).
     The specialised types are then lifted to [listnat'] by the normal pipeline.
     [spec_kn_pairs] : list ((head_kn, [arg_kns]), spec_kn). *)
  let raw_ind_apps :=
    dedup_ind_apps
      (flat_map (fun mwi =>
        flat_map (fun d => collect_ind_apps d.(decl_type)) (snd mwi))
      modes_with_idx) in
  spec_kn_pairs <- monad_fold_left (fun acc entry =>
    let head_kn   := fst entry in
    let arg_kns_e := snd entry in
    head_mind <- tmQuoteInductive head_kn ;;
    if Nat.eqb head_mind.(ind_npars) 0 then tmReturn acc  (* already monomorphic *)
    else
      let spec_name :=
        fold_left (fun s kn => s ++ snd kn) arg_kns_e (snd head_kn) in
      let concrete_args :=
        List.map (fun kn =>
          tInd {| inductive_mind := kn; inductive_ind := 0 |} []) arg_kns_e in
      tmMkInductivePreserveFinite
        (specialize_mind head_mind head_kn concrete_args spec_name) ;;
      refs <- tmLocate spec_name ;;
      let spec_kn :=
        match find (fun g =>
          match g with IndRef _ => true | _ => false end) refs with
        | Some (IndRef ind) => inductive_mind ind
        | _                 => (cur_mp, spec_name)
        end in
      tmReturn (List.app acc [(entry, spec_kn)]))
    raw_ind_apps [] ;;
  let spec_kns := List.map snd spec_kn_pairs in
  (* Step 5: keep only non-Prop, non-parametric types.
     Now includes the freshly declared specialised types (npars = 0). *)
  type_kns <- monad_fold_left (fun acc kn =>
    mind <- tmQuoteInductive kn ;;
    if andb (negb (is_prop_mind mind)) (Nat.eqb mind.(ind_npars) 0)
    then tmReturn (List.app acc [kn])
    else tmReturn acc)
    (List.app arg_kns spec_kns) [] ;;
  let pre_mapping := List.map (fun kn => (kn, (cur_mp, snd kn ++ "'"))) type_kns in
  (* Helper: given a term [t], return the lifted knames it mentions —
     either as a plain [tInd kn] in [pre_mapping], or as a recognised
     parametric application [tApp (tInd head) [tInd arg...]] in [spec_kn_pairs]. *)
  let lookup_lifted_kns t :=
    let spec_hits :=
      flat_map (fun entry =>
        let head_kn   := fst (fst entry) in
        let arg_kns_e := snd (fst entry) in
        let spec_kn   := snd entry in
        flat_map (fun app =>
          if andb (eq_kername (fst app) head_kn)
                  (andb (Nat.eqb #|snd app| #|arg_kns_e|)
                        (forallb (fun ab => eq_kername (fst ab) (snd ab))
                                 (combine (snd app) arg_kns_e)))
          then [spec_kn]
          else [])
        (collect_ind_apps t))
      spec_kn_pairs in
    let plain_hits :=
      filter (fun kn => existsb (fun p => eq_kername kn (fst p)) pre_mapping)
             (collect_tind_kns t) in
    dedup_kns (List.app spec_hits plain_hits) in
  (* Mode-derived dep edges: output types must come after their input types
     so that extra constructors can reference already-declared lifted inputs.
     We use only plain type deps here (not spec_hits) to avoid spurious cycles:
     extra constructors fall back to parametric types (e.g. [list nat']) rather
     than specialised ones (e.g. [listnat']) when the spec type is not yet
     declared, so the only ordering constraint is on the COMPONENT plain types. *)
  let plain_get_lifted_kns idx_ctx n_idx pos :=
    let snoc_p := n_idx - 1 - pos in
    match nth_error idx_ctx snoc_p with
    | None   => []
    | Some d =>
      filter (fun kn => existsb (fun p => eq_kername kn (fst p)) pre_mapping)
             (collect_tind_kns d.(decl_type))
    end in
  let mode_dep_pairs :=
    flat_map (fun mwi =>
      let in_pos  := fst (snd (fst mwi)) in
      let out_pos := snd (snd (fst mwi)) in
      let idx_ctx := snd mwi in
      let n_idx   := #|idx_ctx| in
      let input_kns := dedup_kns (flat_map (plain_get_lifted_kns idx_ctx n_idx) in_pos) in
      flat_map (fun op =>
        flat_map (fun out_kn =>
          List.map (fun in_kn => (out_kn, in_kn))
            (filter (fun in_kn => negb (eq_kername in_kn out_kn)) input_kns))
        (plain_get_lifted_kns idx_ctx n_idx op))
      out_pos)
    modes_with_idx in
  type_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;;
    tmReturn (kn, mind))
    type_kns ;;
  let sorted_kns :=
    topo_sort_kns type_kns type_minds pre_mapping mode_dep_pairs [] (S #|type_kns|) in
  (* Step 6: declare lifted types, grouping mutually dependent ones into a
     single mutual inductive block so forward-reference anomalies are avoided.
     Phase a: pre-compute full ind_mapping (all new kns, ind=0 placeholder).
     Phase b: pre-compute full app_kn_mapping from spec_kn_pairs.
     Phase c: compute all lifted bodies with the full mapping.
     Phase d: detect cross-type deps, group into connected components.
     Phase e: declare each group as a mutual block. *)
  let pre_ind_mapping :=
    List.map (fun kn =>
      (kn, {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |}))
    type_kns in
  let pre_app_kn_mapping :=
    flat_map (fun e =>
      let head_kn   := fst (fst e) in
      let arg_kns_e := snd (fst e) in
      let spec_kn   := snd e in
      match find (fun p => eq_kername (fst p) spec_kn) pre_ind_mapping with
      | Some (_, lifted_ind) => [((head_kn, arg_kns_e), lifted_ind)]
      | None => []
      end)
    spec_kn_pairs in
  computed_bodies <- monad_fold_left (fun acc kn =>
    match find (fun p => eq_kername (fst p) kn) type_minds with
    | None => tmFail "preprocess_coind_types: topo sort internal error"
    | Some (_, old_mind) =>
      let pre_new_ind :=
        {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |} in
      let ext := filter (fun q => negb (eq_kername (fst q) kn)) pre_ind_mapping in
      let body :=
        make_lifted_mind old_mind kn pre_new_ind ext
          pre_app_kn_mapping spec_kn_pairs modes_with_idx 1 0 in
      tmReturn (List.app acc [(kn, body)])
    end)
  sorted_kns [] ;;
  let new_kn_to_old :=
    List.map (fun p => (inductive_mind (snd p), fst p)) pre_ind_mapping in
  let dep_edges :=
    flat_map (fun entry =>
      let self_kn  := fst entry in
      let body     := snd entry in
      let body_kns := collect_kns_from_mind body in
      flat_map (fun bkn =>
        match find (fun p => eq_kername (fst p) bkn) new_kn_to_old with
        | Some (_, old_kn) =>
          if eq_kername old_kn self_kn then [] else [(self_kn, old_kn)]
        | None => []
        end)
      body_kns)
    computed_bodies in
  let orig_groups := group_connected_components sorted_kns dep_edges in
  (* Reject circular dependencies between Inductive and CoInductive types: Rocq
     does not allow mixed mutual blocks, and if A (Finite) and B (CoFinite)
     reference each other, neither can be declared first without a forward ref.
     Detect this: a mixed connected component with dep_edges in BOTH directions. *)
  _ <- monad_fold_left (fun _ grp =>
    let cofinite := filter (fun kn =>
      match find (fun p => eq_kername (fst p) kn) type_minds with
      | Some (_, m) => match m.(ind_finite) with CoFinite => true | _ => false end
      | None        => false
      end) grp in
    let finite := filter (fun kn =>
      negb (existsb (eq_kername kn) cofinite)) grp in
    match cofinite, finite with
    | [], _ | _, [] => tmReturn tt
    | _,  _ =>
      let cf_refs_f := existsb (fun e =>
        andb (existsb (eq_kername (fst e)) cofinite)
             (existsb (eq_kername (snd e)) finite)) dep_edges in
      let f_refs_cf := existsb (fun e =>
        andb (existsb (eq_kername (fst e)) finite)
             (existsb (eq_kername (snd e)) cofinite)) dep_edges in
      if andb cf_refs_f f_refs_cf
      then tmFail ("cannot handle inductive/co-inductive type dependency: " ++
                   fold_left (fun s kn => s ++ " " ++ snd kn) cofinite "(CoInductive)" ++
                   " <-> " ++
                   fold_left (fun s kn => s ++ " " ++ snd kn) finite "(Inductive)")
      else tmReturn tt
    end)
  orig_groups tt ;;
  (* Split groups that mix Finite and CoFinite types: Rocq forbids mixed
     mutual blocks, and a group whose first member is Finite would silently
     make a CoInductive type (e.g. stream') appear as Inductive. *)
  let groups :=
    flat_map (fun grp =>
      let cofinite := filter (fun kn =>
        match find (fun p => eq_kername (fst p) kn) type_minds with
        | Some (_, m) => match m.(ind_finite) with CoFinite => true | _ => false end
        | None        => false
        end) grp in
      let finite := filter (fun kn =>
        negb (existsb (eq_kername kn) cofinite)) grp in
      match cofinite, finite with
      | [], _ | _, [] => [grp]
      | _,  _         => [cofinite; finite]
      end) orig_groups in
  let sorted_groups :=
    snd (fold_left (fun acc kn =>
      let seen   := fst acc in
      let result := snd acc in
      if existsb (eq_kername kn) seen then (seen, result)
      else
        let grp :=
          match find (fun g => existsb (eq_kername kn) g) groups with
          | Some g => g
          | None   => [kn]
          end in
        let grp_sorted :=
          filter (fun kn' => existsb (eq_kername kn') grp) sorted_kns in
        (dedup_kns (List.app seen grp), List.app result [grp_sorted]))
    sorted_kns ([] : list kername, [] : list (list kername))) in
  actual_mapping <- monad_fold_left (fun acc grp =>
    match grp with
    | [] => tmReturn acc
    | first_kn :: _ =>
      let block_kn := (cur_mp, snd first_kn ++ "'") in
      let block_n_bodies := #|grp| in
      (* Map each group member to its correct block inductive (kn → {mind=block_kn, ind=j}) *)
      let group_ind_mapping :=
        snd (fold_left (fun st kn_j =>
          let j       := fst st in
          let acc_gim := snd st in
          (S j, List.app acc_gim
            [(kn_j, {| inductive_mind := block_kn; inductive_ind := j |})]))
        grp (0, [])) in
      (* Build a corrected app_kn_mapping for this group: replace any pre-mapping entry
         whose target spec inductive is a group member with the correct block inductive.
         This ensures extra constructors reference, e.g., {mind:block_kn,ind:2} for
         listnat' rather than the stale standalone placeholder {mind:(mp,"listnat'"),ind:0}.
         For spec types outside this group, use [acc] (already-declared actual mappings)
         rather than [pre_ind_mapping], since [pre_ind_mapping] carries stale knames when
         a previously-declared group was combined under a different block_kn. *)
      let grp_app_kn_mapping :=
        flat_map (fun e =>
          let head_kn   := fst (fst e) in
          let arg_kns_e := snd (fst e) in
          let spec_kn   := snd e in
          match find (fun p => eq_kername (fst p) spec_kn) group_ind_mapping with
          | Some (_, grp_ind) => [((head_kn, arg_kns_e), grp_ind)]
          | None =>
            match find (fun p => eq_kername (fst p) spec_kn) acc with
            | Some (_, acc_ind) => [((head_kn, arg_kns_e), acc_ind)]
            | None => []
            end
          end)
        spec_kn_pairs in
      (* Second-pass: recompute each body with the correct block-level de Bruijn indices *)
      let all_bodies :=
        snd (fold_left (fun st kn_i =>
          let block_body_offset := fst st in
          let bodies_so_far     := snd st in
          match find (fun p => eq_kername (fst p) kn_i) type_minds with
          | None => (S block_body_offset, bodies_so_far)
          | Some (_, old_mind_i) =>
            let pre_new_ind_i :=
              {| inductive_mind := block_kn; inductive_ind := block_body_offset |} in
            (* ext: other group members at correct block indices + types outside this group.
               Use [acc] (already-declared actual inds) for external types so that we get
               the real block kname ({mind:"bool'",ind:1} for nat') rather than the stale
               pre_ind_mapping placeholder ({mind:"nat'",ind:0}). *)
            let ext_i :=
              List.app
                (filter (fun q => negb (eq_kername (fst q) kn_i)) group_ind_mapping)
                (filter (fun q => negb (existsb (eq_kername (fst q)) grp)) acc) in
            let m := make_lifted_mind old_mind_i kn_i pre_new_ind_i ext_i
                       grp_app_kn_mapping spec_kn_pairs modes_with_idx
                       block_n_bodies block_body_offset in
            (S block_body_offset, List.app bodies_so_far m.(ind_bodies))
          end)
        grp (0, [])) in
      let block_finite :=
        match find (fun p => eq_kername (fst p) first_kn) type_minds with
        | Some (_, m) => m.(ind_finite)
        | None        => Finite
        end in
      let block_universes :=
        match find (fun p => eq_kername (fst p) first_kn) type_minds with
        | Some (_, m) => m.(ind_universes)
        | None        => Monomorphic_ctx
        end in
      let combined :=
        {| ind_finite    := block_finite;
           ind_npars     := 0;
           ind_universes := block_universes;
           ind_variance  := None;
           ind_params    := [];
           ind_bodies    := all_bodies |} in
      tmMkInductivePreserveFinite combined ;;
      actual_inds <- monad_map (fun kn_i =>
        let short_nm := snd kn_i ++ "'" in
        refs <- tmLocate short_nm ;;
        let ai :=
          match find (fun g => match g with IndRef _ => true | _ => false end) refs with
          | Some (IndRef ind) => ind
          | _ => {| inductive_mind := (cur_mp, short_nm); inductive_ind := 0 |}
          end in
        tmReturn (kn_i, ai))
      grp ;;
      tmReturn (List.app acc actual_inds)
    end)
  sorted_groups [] ;;
  let final_app_kn_mapping :=
    flat_map (fun e =>
      let head_kn   := fst (fst e) in
      let arg_kns_e := snd (fst e) in
      let spec_kn   := snd e in
      match find (fun p => eq_kername (fst p) spec_kn) actual_mapping with
      | Some (_, lifted_ind) => [((head_kn, arg_kns_e), lifted_ind)]
      | None => []
      end)
    spec_kn_pairs in
  tmReturn (actual_mapping, final_app_kn_mapping).


(* ================================================================== *)
(** ** Lifting relations over lifted types                            *)
(* ================================================================== *)

(** Resolve an inductive's kername by short name via [tmLocate]. *)
Definition tmLocateInd (nm : string) : TemplateMonad kername :=
  refs <- tmLocate nm ;;
  match find (fun g => match g with IndRef _ => true | _ => false end) refs with
  | Some (IndRef ind) => tmReturn (inductive_mind ind)
  | _ => tmFail ("tmLocateInd: cannot find inductive '" ++ nm ++ "'")
  end.

(** Match [tApp (tConstruct head_ind ctor_idx _) [type_arg1; ... val_args]]
    against [app_kn_mapping].  The first [|arg_kns|] arguments are type
    parameters (expected to be bare [tInd] nodes matching the recorded arg kns);
    the rest are value arguments.
    Returns [(lifted_spec_kn, n_params)] when the constructor belongs to a
    parametric type that was monomorphised: the caller strips [n_params] leading
    args and routes the value args to the specialised constructor. *)
Definition lookup_ctor_app_kn
    (app_kn_mapping : list (kername * list kername * inductive))
    (f : term) (args : list term)
    : option (inductive * nat) :=
  match f with
  | tConstruct ind _ _ =>
    let head_kn := inductive_mind ind in
    match find (fun e => eq_kername (fst (fst e)) head_kn) app_kn_mapping with
    | None => None
    | Some e =>
      let arg_kns  := snd (fst e) in
      let n_params := #|arg_kns| in
      if Nat.leb n_params #|args| then
        let type_args := firstn n_params args in
        if forallb (fun a => match a with tInd _ _ => true | _ => false end) type_args then
          let type_arg_kns :=
            flat_map (fun a => match a with
                               | tInd i _ => [inductive_mind i]
                               | _        => []
                               end) type_args in
          if andb (Nat.eqb #|type_arg_kns| #|arg_kns|)
                  (forallb (fun ab => eq_kername (fst ab) (snd ab))
                           (combine arg_kns type_arg_kns))
          then Some (snd e, n_params)
          else None
        else None
      else None
    end
  | _ => None
  end.

(** Substitute both [tInd] and [tConstruct] knames throughout a term.
    Also resolves parametric-type applications via [app_kn_mapping]:
    [tApp (tInd head_kn _) [tInd arg_kn _; ...]] → [tInd lifted_spec_kn []]
    when a monomorphic specialisation exists.  The [tApp] check runs BEFORE
    recursive descent so original arg knames are used for the lookup. *)
Fixpoint subst_inds_and_ctors
    (app_kn_mapping : list (kername * list kername * inductive))
    (mapping        : list (kername * inductive))
    (t              : term) : term :=
  let sub := subst_inds_and_ctors app_kn_mapping mapping in
  let lookup ind :=
    match find (fun p => eq_kername (fst p) (inductive_mind ind)) mapping with
    | Some (_, ind') => ind'
    | None           => ind
    end in
  match t with
  | tInd ind univs =>
    tInd (lookup ind) univs
  | tConstruct ind idx univs =>
    tConstruct (lookup ind) idx univs
  | tApp f args =>
    match lookup_app_kn_ind app_kn_mapping f args with
    | Some lifted_ind =>
      tInd lifted_ind []
    | None =>
      match lookup_ctor_app_kn app_kn_mapping f args with
      | Some (lifted_ind, n_params) =>
        (* Substitute all args (elements are structural subterms), then strip
           the first [n_params] type-parameter positions from the result. *)
        let args_sub  := List.map sub args in
        let val_args  := skipn n_params args_sub in
        let new_ctor  :=
          match f with
          | tConstruct _ idx univs =>
            tConstruct lifted_ind idx univs
          | _ => sub f
          end in
        match val_args with
        | [] => new_ctor
        | _  => tApp new_ctor val_args
        end
      | None =>
        tApp (sub f) (List.map sub args)
      end
    end
  | tEvar n args         => tEvar n (List.map sub args)
  | tCast c k v          => tCast (sub c) k (sub v)
  | tProd na ty body     => tProd na (sub ty) (sub body)
  | tLambda na ty body   => tLambda na (sub ty) (sub body)
  | tLetIn na val ty body => tLetIn na (sub val) (sub ty) (sub body)
  | tCase ci pred disc brs =>
    let ci' :=
      {| ci_ind      := lookup ci.(ci_ind);
         ci_npar      := ci.(ci_npar);
         ci_relevance := ci.(ci_relevance) |} in
    let pred' :=
      {| pparams  := List.map sub pred.(pparams);
         puinst   := pred.(puinst);
         pcontext := pred.(pcontext);
         preturn  := sub pred.(preturn) |} in
    tCase ci' pred' (sub disc)
      (List.map (fun br =>
        {| bcontext := br.(bcontext); bbody := sub br.(bbody) |}) brs)
  | tProj p c     => tProj p (sub c)
  | tFix mfix idx =>
    tFix (List.map (fun d =>
      {| dname := d.(dname); dtype := sub d.(dtype);
         dbody := sub d.(dbody); rarg := d.(rarg) |}) mfix) idx
  | tCoFix mfix idx =>
    tCoFix (List.map (fun d =>
      {| dname := d.(dname); dtype := sub d.(dtype);
         dbody := sub d.(dbody); rarg := d.(rarg) |}) mfix) idx
  | _ => t
  end.

Definition subst_inds_and_ctors_decl
    (app_kn_mapping : list (kername * list kername * inductive))
    (mapping        : list (kername * inductive))
    (d              : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map (subst_inds_and_ctors app_kn_mapping mapping) d.(decl_body);
     decl_type := subst_inds_and_ctors app_kn_mapping mapping d.(decl_type) |}.

(** Find the 0-based index of a constructor by name in a constructor list. *)
Fixpoint find_ctor_idx (nm : string) (ctors : list constructor_body) (acc : nat)
    : option nat :=
  match ctors with
  | [] => None
  | c :: rest =>
    if String.eqb c.(cstr_name) nm then Some acc
    else find_ctor_idx nm rest (S acc)
  end.

(** Find the 0-based index of [x] in a list of nats. *)
Fixpoint find_nat_idx (x : nat) (l : list nat) (acc : nat) : option nat :=
  match l with
  | [] => None
  | y :: rest =>
    if Nat.eqb x y then Some acc
    else find_nat_idx x rest (S acc)
  end.

(** Compute the [<rel>'Undefined] constructor for one body of the lifted
    relation block.

    The constructor universally quantifies over all input-position variables
    and maps every output position to the extra constructor of the lifted
    data type (named [relNm ++ "An" ++ pos]) applied to those inputs.
    Example: [Integrate'Undefined : forall v0, Integrate' v0 (IntegrateAn1 v0)].

    de Bruijn convention (same as [compute_extra_cstrs]):
      - cstr_type = [it_mkProd_or_LetIn input_decls return_t].
      - in input_decls (snoc order), the j-th input (= in_pos[j]'s var) is
        at [tRel (n_params + n_inputs - 1 - j)] in return_t.
      - input_var_list = [tRel(n_params+n_inputs-1); ...; tRel n_params]
        = [v0; v1; ...] in in_pos order (v0 outermost).
      - body [body_idx] of the mutual block is at
        [tRel (n_params + n_inputs + n_bodies - 1 - body_idx)] in return_t. *)
Definition compute_undefined_cstr
    (oib            : one_inductive_body)
    (body_idx       : nat)
    (n_params       : nat)
    (n_bodies       : nat)
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list kername * inductive))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    (type_body_map  : list (inductive * one_inductive_body))
    : list constructor_body :=
  match find (fun mwi => String.eqb (fst (fst mwi)) oib.(ind_name)) modes_with_idx with
  | None => []
  | Some mwi =>
    let in_pos   := fst (snd (fst mwi)) in
    let out_pos  := snd (snd (fst mwi)) in
    let idx_ctx  := snd mwi in
    let n_idx    := #|idx_ctx| in
    let n_inputs := #|in_pos| in
    let input_decls :=
      List.rev (snd (fold_left (fun da ip =>
        let snoc_ip := n_idx - 1 - ip in
        match nth_error idx_ctx snoc_ip with
        | None => (S (fst da), snd da)
        | Some d =>
          (S (fst da), List.app (snd da)
            [{| decl_name := d.(decl_name);
                decl_body := None;
                decl_type :=
                  subst_inds_and_ctors app_kn_mapping type_mapping d.(decl_type) |}])
        end)
      in_pos (0, []))) in
    let input_var_list := List.map tRel (List.rev (seq n_params n_inputs)) in
    let arg_terms :=
      List.map (fun pos =>
        match find_nat_idx pos in_pos 0 with
        | Some j =>
          tRel (n_params + n_inputs - 1 - j)
        | None =>
          if existsb (Nat.eqb pos) out_pos then
            let extra_nm := oib.(ind_name) ++ "An" ++ string_of_nat pos in
            let snoc_pos := n_idx - 1 - pos in
            match nth_error idx_ctx snoc_pos with
            | None => tVar "error_idx"
            | Some d =>
              (* Resolve the output type: parametric apps (e.g. [list nat])
                 take priority via [app_kn_mapping]; plain [tInd] kns fall
                 back to [type_mapping].  Result is [option inductive] so
                 that mutual-block body indices are preserved exactly. *)
              let resolved_new_ind :=
                match collect_ind_apps d.(decl_type) with
                | app :: _ =>
                  match find (fun e =>
                    andb (eq_kername (fst (fst e)) (fst app))
                         (andb (Nat.eqb #|snd (fst e)| #|snd app|)
                               (forallb (fun ab => eq_kername (fst ab) (snd ab))
                                        (combine (snd (fst e)) (snd app)))))
                    app_kn_mapping with
                  | Some e => Some (snd e)  (* snd e : inductive *)
                  | None   => None
                  end
                | [] => None
                end in
              match (match resolved_new_ind with
                     | Some ind => Some ind
                     | None =>
                       match collect_tind_kns d.(decl_type) with
                       | [] => None
                       | old_kn :: _ =>
                         match find (fun p => eq_kername (fst p) old_kn) type_mapping with
                         | Some (_, i) => Some i  (* full inductive, preserves ind *)
                         | None        =>
                           Some {| inductive_mind := old_kn; inductive_ind := 0 |}
                         end
                       end
                     end) with
              | None => tVar "error_no_type"
              | Some new_ind =>
                let eq_ind a b :=
                  andb (eq_kername (inductive_mind a) (inductive_mind b))
                       (Nat.eqb (inductive_ind a) (inductive_ind b)) in
                match find (fun p => eq_ind (fst p) new_ind) type_body_map with
                | Some (_, new_oib) =>
                  (* Lifted type: use the extra "An" constructor with input values *)
                  let ctor_idx :=
                    match find_ctor_idx extra_nm new_oib.(ind_ctors) 0 with
                    | Some i => i
                    | None   => 0
                    end in
                  if Nat.eqb n_inputs 0
                  then tConstruct new_ind ctor_idx []
                  else tApp (tConstruct new_ind ctor_idx []) input_var_list
                | None =>
                  (* Non-lifted parametric type (e.g. list nat'): use constructor 0
                     applied to the TYPE ARGUMENTS of the substituted output type.
                     For [list nat'] this yields [@nil nat' : list nat']. *)
                  let subst_t :=
                    subst_inds_and_ctors app_kn_mapping type_mapping d.(decl_type) in
                  match subst_t with
                  | tApp _ type_args => tApp (tConstruct new_ind 0 []) type_args
                  | _                => tConstruct new_ind 0 []
                  end
                end
              end
            end
          else
            tVar "error_unmapped_pos"
        end)
      (seq 0 n_idx) in
    let self_rel  := n_params + n_inputs + n_bodies - 1 - body_idx in
    let return_t  := tApp (tRel self_rel) arg_terms in
    let cstr_type := it_mkProd_or_LetIn input_decls return_t in
    [{| cstr_name    := oib.(ind_name) ++ "'Undefined";
        cstr_args    := input_decls;
        cstr_indices := [];
        cstr_type    := cstr_type;
        cstr_arity   := n_inputs |}]
  end.

(** Build the lifted [mutual_inductive_body] for a relation block,
    appending a [<rel>'Undefined] constructor to every body. *)
Definition make_lifted_relation_mind
    (old_mind       : mutual_inductive_body)
    (old_rel_kn     : kername)
    (new_rel_kn     : kername)
    (rel_mapping    : list (kername * inductive))
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list kername * inductive))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    (type_body_map  : list (inductive * one_inductive_body))
    : mutual_inductive_body :=
  let new_rel_ind  := {| inductive_mind := new_rel_kn; inductive_ind := 0 |} in
  let full_mapping := (old_rel_kn, new_rel_ind) :: rel_mapping ++ type_mapping in
  let params'  := List.map (subst_inds_and_ctors_decl app_kn_mapping full_mapping) old_mind.(ind_params) in
  let n_params := #|params'| in
  let n_bodies := #|old_mind.(ind_bodies)| in
  {| ind_finite    := old_mind.(ind_finite);
     ind_npars     := old_mind.(ind_npars);
     ind_universes := old_mind.(ind_universes);
     ind_variance  := old_mind.(ind_variance);
     ind_params    := params';
     ind_bodies    :=
       mapi (fun i oib =>
         let undef :=
           compute_undefined_cstr oib i n_params n_bodies
             type_mapping app_kn_mapping modes_with_idx type_body_map in
         {| ind_name      := oib.(ind_name) ++ "'";
            ind_indices   := List.map (subst_inds_and_ctors_decl app_kn_mapping full_mapping) oib.(ind_indices);
            ind_sort      := oib.(ind_sort);
            ind_type      := subst_inds_and_ctors app_kn_mapping full_mapping oib.(ind_type);
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              List.map (fun c =>
                {| cstr_name    := c.(cstr_name) ++ "'";
                   cstr_args    := List.map (subst_inds_and_ctors_decl app_kn_mapping full_mapping) c.(cstr_args);
                   cstr_indices := List.map (subst_inds_and_ctors app_kn_mapping full_mapping) c.(cstr_indices);
                   cstr_type    := subst_inds_and_ctors app_kn_mapping full_mapping c.(cstr_type);
                   cstr_arity   := c.(cstr_arity) |})
              oib.(ind_ctors) ++ undef;
            ind_projs     := oib.(ind_projs);
            ind_relevance := oib.(ind_relevance) |})
       old_mind.(ind_bodies) |}.

(** Declare the lifted version of a mutual relation block.
    [modes] supplies the input/output positions for each body, used to
    build the Undefined constructors. *)
Polymorphic Definition lift_relation
    (rel_kn         : kername)
    (rel_mapping    : list (kername * inductive))
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list kername * inductive))
    (modes          : mode_map)
    : TemplateMonad unit :=
  cur_mp   <- tmCurrentModPath tt ;;
  old_mind <- tmQuoteInductive rel_kn ;;
  let new_rel_kn := (cur_mp, snd rel_kn ++ "'") in
  let modes_with_idx :=
    List.map (fun me =>
      let nm     := fst me in
      let in_out := snd me in
      let idx_ctx :=
        match find (fun oib => String.eqb oib.(ind_name) nm) old_mind.(ind_bodies) with
        | Some oib => oib.(ind_indices)
        | None     => []
        end in
      ((nm, in_out), idx_ctx))
    modes in
  type_body_map <- monad_map (fun p =>
    let new_ind := snd p in
    new_mind <- tmQuoteInductive (inductive_mind new_ind) ;;
    match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
    | Some oib => tmReturn (new_ind, oib)
    | None     => @tmFail (inductive * one_inductive_body) "lift_relation: empty lifted type"
    end)
    type_mapping ;;
  tmMkInductivePreserveFinite
    (make_lifted_relation_mind old_mind rel_kn new_rel_kn rel_mapping type_mapping
       app_kn_mapping modes_with_idx type_body_map).


(** Convert [k1; k2; k3; k4; ...] into [(k1,k2); (k3,k4); ...]. *)
Fixpoint pair_up {A : Type} (l : list A) : list (A * A) :=
  match l with
  | x :: y :: rest => (x, y) :: pair_up rest
  | _ => []
  end.

(** Resolve string names and lift a mutual relation block.
    [rel_nm]      : short name of the relation block (e.g. "Integrate").
    [type_nm_map] : pairs of (old-type-name, lifted-type-name).
    [modes]       : input/output positions for each body.

    Kname resolution uses the same proven [monad_fold_left] pattern as
    [preprocess_coind_types]: all names are collected in one pass in
    the order [rel; old1; new1; old2; new2; ...], then [pair_up]
    reconstructs the type-mapping list. *)
Polymorphic Definition lift_relation_names
    (rel_nm      : string)
    (type_nm_map : list (string * string))
    (modes       : mode_map)
    : TemplateMonad unit :=
  let all_nms :=
    rel_nm :: List.concat (List.map (fun p => [fst p; snd p]) type_nm_map) in
  inds <- monad_fold_left (fun acc nm =>
    refs <- tmLocate nm ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [ind])
    | _ => tmFail ("lift_relation_names: cannot find '" ++ nm ++ "'")
    end)
    all_nms [] ;;
  match inds return TemplateMonad unit with
  | rel_ind :: inds_rest =>
    (* Pair up (old_ind, new_ind); map key is old inductive_mind *)
    let type_mapping :=
      List.map (fun p => (inductive_mind (fst p), snd p)) (pair_up inds_rest) in
    lift_relation (inductive_mind rel_ind) [] type_mapping [] modes
  | _ => @tmFail unit "lift_relation_names: failed to resolve knames"
  end.

(** Combined entry point: lift all coinductive types referenced by [modes]
    and then lift the relation itself, in a single [MetaRocq Run].
    [rel_nm] : short name of the top-level relation (e.g. "Integrate").
    [modes]  : input/output positions for every body of the mutual block. *)
Polymorphic Definition lift_coinductive_relation
    (rel_nm : string)
    (modes  : mode_map)
    : TemplateMonad unit :=
  (* Resolve every mode entry to its mutual-block kname, in order. *)
  kn_mode_list <- monad_fold_left (fun acc me =>
    refs <- tmLocate (fst me) ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [(inductive_mind ind, me)])
    | _ => tmFail ("lift_coinductive_relation: cannot find '" ++ fst me ++ "'")
    end)
    modes [] ;;
  match kn_mode_list return TemplateMonad unit with
  | [] => @tmFail unit "lift_coinductive_relation: no modes provided"
  | _  =>
    preproc_result <- preprocess_coind_types modes ;;
    let type_mapping   := fst preproc_result in
    let app_kn_mapping := snd preproc_result in
    cur_mp <- tmCurrentModPath tt ;;
    (* Deduplicate block knames, preserving order of first appearance. *)
    let unique_block_kns :=
      fold_left (fun acc p =>
        if existsb (eq_kername (fst p)) acc then acc
        else List.app acc [fst p])
      kn_mode_list [] in
    (* Pre-compute new inductives for all relation blocks so cross-block references
       in constructor types are substituted correctly when lifting each block. *)
    let rel_mapping :=
      List.map (fun kn =>
        (kn, {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |}))
        unique_block_kns in
    monad_fold_left (fun _ block_kn =>
      let block_modes :=
        List.map snd (filter (fun p => eq_kername (fst p) block_kn) kn_mode_list) in
      lift_relation block_kn rel_mapping type_mapping app_kn_mapping block_modes)
      unique_block_kns tt
  end.
  



(* ================================================================== *)
(** ** Example: all relations (single mutual block + separate blocks)  *)
(*                                                                      *)
(*  Integrate / addStm / addNat are declared with [with], so they      *)
(*  form one mutual inductive block.                                    *)
(*  isZero and Len are declared in two separate [Inductive] commands,  *)
(*  so lift_coinductive_relation must handle multiple blocks.           *)
(* ================================================================== *)


Unset Universe Checking.

MetaRocq Run (lift_coinductive_relation "Integrate"
               [("Integrate", ([0],   [1]));
                ("addStm",    ([0;1], [2]));
                ("addNat",    ([0;1], [2]));
                ("isZero",    ([0],   [1]));
                ("Len",       ([0],   [1;2]))]).
Set Universe Checking.


Parameter IntegrateAn1fnSymb : stream -> stream.
Parameter addStmAn2fnSymb : nat -> stream -> stream.
Parameter addNatAn2fnSymb : nat -> nat -> nat.
Parameter isZeroAn1fnSymb : bool -> nat.
Parameter LenAn2fnSymb : list nat -> nat.

Parameter LenAn1fnSymb : list nat -> list nat. 

Print nat'.



Definition boolLift (b : bool) : bool' :=
match b with
| true => true'
| false => false'
end.

Fixpoint natLift (n : nat) : nat' :=
match n with
| 0 => O'
| S m => S' (natLift m)
end.

Fixpoint listnatLift (l : list nat) : listnat' :=
match l with
| [] => listnat_nil'
| v0 :: l' => listnat_cons' (natLift v0) (listnatLift l')
end.
Print stream'.

CoFixpoint streamLift (s : stream) : stream' :=
match s with
| nil => nil'
| Seq v0 v1 => Seq' (natLift v0) (streamLift v1)
end.

Print stream.






 


        
                
                
                
                
                
                
                
                
                
                
                
                
                
                
                
                
                              