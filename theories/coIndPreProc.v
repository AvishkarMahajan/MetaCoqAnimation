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




(*
MetaRocq Run (animate_coinductive <? Integrate ?>
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

(** Collect the kname of the TYPE argument [T] of every [@eq T t1 t2]
    application anywhere in [t]. Used to find types that appear in equality
    premises of relation constructors — these also need lifting. *)
Fixpoint collect_eq_arg_kns (t : term) : list kername :=
  match t with
  | tApp f args =>
    let eq_hits :=
      match f with
      | tInd {| inductive_mind := kn |} _ =>
        if String.eqb (snd kn) "eq" then
          match args with T :: _ => collect_tind_kns T | [] => [] end
        else []
      | _ => []
      end in
    eq_hits ++ collect_eq_arg_kns f ++ flat_map collect_eq_arg_kns args
  | tProd   _ ty body
  | tLambda _ ty body    => collect_eq_arg_kns ty ++ collect_eq_arg_kns body
  | tLetIn  _ v ty body  =>
    collect_eq_arg_kns v ++ collect_eq_arg_kns ty ++ collect_eq_arg_kns body
  | tCase _ pred disc brs =>
    flat_map collect_eq_arg_kns pred.(pparams) ++
    collect_eq_arg_kns pred.(preturn) ++
    collect_eq_arg_kns disc ++
    flat_map (fun br => collect_eq_arg_kns br.(bbody)) brs
  | _ => []
  end.

(** Like [collect_eq_arg_kns] but returns [(head_kn, [arg_kns])] pairs for
    parametric-type applications inside each equality TYPE argument.
    Needed so that e.g. [@eq (list nat) ...] triggers monomorphisation of
    [list nat] → [listnat] via the Step 4b pipeline. *)
Fixpoint collect_eq_arg_ind_apps (t : term) : list (kername * list kername) :=
  match t with
  | tApp f args =>
    let eq_hits :=
      match f with
      | tInd {| inductive_mind := kn |} _ =>
        if String.eqb (snd kn) "eq" then
          match args with T :: _ => collect_ind_apps T | [] => [] end
        else []
      | _ => []
      end in
    eq_hits ++ collect_eq_arg_ind_apps f ++ flat_map collect_eq_arg_ind_apps args
  | tProd   _ ty body
  | tLambda _ ty body    => collect_eq_arg_ind_apps ty ++ collect_eq_arg_ind_apps body
  | tLetIn  _ v ty body  =>
    collect_eq_arg_ind_apps v ++ collect_eq_arg_ind_apps ty ++
    collect_eq_arg_ind_apps body
  | tCase _ pred disc brs =>
    flat_map collect_eq_arg_ind_apps pred.(pparams) ++
    collect_eq_arg_ind_apps pred.(preturn) ++
    collect_eq_arg_ind_apps disc ++
    flat_map (fun br => collect_eq_arg_ind_apps br.(bbody)) brs
  | _ => []
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
                let nm' :=
                  match binder_name d.(decl_name) with
                  | nNamed _ => d.(decl_name)
                  | nAnon    =>
                    {| binder_name     := nNamed ("v" ++ string_of_nat (List.length acc));
                       binder_relevance := binder_relevance d.(decl_name) |}
                  end in
                (S depth, List.app acc
                   [{| decl_name := nm';
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

(** BFS from [lifting], exploring constructor-argument types of each visited
    type.  A newly-discovered type B is added to [lifting] iff at least one
    of B's constructor argument types is already in [lifting] (B "depends on"
    a lifted type).  [explored] prevents revisiting.  [rel_kns] are never
    added to [lifting].  Handles multi-hop chains: if B → C → T ∈ lifting,
    then C is added first (when T's constructors are explored) and B is added
    later (when C's constructors are explored and C ∈ lifting). *)
Polymorphic Fixpoint expand_dep_closure
    (worklist : list kername)
    (lifting  : list kername)
    (explored : list kername)
    (rel_kns  : list kername)
    (fuel     : nat)
    : TemplateMonad (list kername) :=
  match fuel with
  | 0 => tmReturn lifting
  | S f =>
    match worklist with
    | [] => tmReturn lifting
    | kn :: rest =>
      if orb (existsb (eq_kername kn) explored)
             (existsb (eq_kername kn) rel_kns)
      then expand_dep_closure rest lifting explored rel_kns f
      else
        mind <- tmQuoteInductive kn ;;
        if orb (is_prop_mind mind) (negb (Nat.eqb mind.(ind_npars) 0))
        then expand_dep_closure rest lifting
               (dedup_kns (explored ++ [kn])) rel_kns f
        else
          let ctor_arg_kns :=
            dedup_kns (flat_map (fun oib =>
              flat_map (fun c => collect_tind_kns c.(cstr_type))
                       oib.(ind_ctors))
            mind.(ind_bodies)) in
          let new_in_wl :=
            filter (fun kn' =>
              andb (negb (existsb (eq_kername kn') explored))
                   (negb (existsb (eq_kername kn') rest)))
              ctor_arg_kns in
          let new_lifting :=
            if andb (negb (existsb (eq_kername kn) lifting))
                    (existsb (fun kn' =>
                       existsb (eq_kername kn') lifting) ctor_arg_kns)
            then dedup_kns (lifting ++ [kn])
            else lifting in
          expand_dep_closure
            (rest ++ new_in_wl)
            new_lifting
            (dedup_kns (explored ++ [kn]))
            rel_kns f
    end
  end.

(** Given a [mode_map], find all non-Prop types occurring as argument types
    of the listed relations, declare lifted copies, and return:
    - [type_mapping]   : old kname → new kname for each lifted data type
    - [app_kn_mapping] : (head_kn, [arg_kns], lifted_spec_kn) for each
      parametric application (e.g. [list nat]) that was monomorphised to a
      fresh inductive (e.g. [listnat']) before lifting.

    Parametric-type applications found in index types are specialised first
    (Step 4b) and then lifted by the same pipeline as monomorphic types. *)
Unset Universe Checking.
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
  (* Step 3.5: collect types from equality premises in relation constructors.
     Types appearing as [T] in [@eq T t1 t2] premises need lifting even when
     they don't appear in the relation's index signature. *)
  let ctor_eq_kns_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_kns c.(cstr_type))
                 oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds in
  let ctor_eq_ind_apps_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_ind_apps c.(cstr_type))
                 oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds in
  (* Step 4: collect all tInd knames from every index-type decl,
     merged with equality-premise types from Step 3.5. *)
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
    dedup_kns (filter (fun kn => negb (existsb (eq_kername kn) rel_kns))
              (List.app arg_kns_raw ctor_eq_kns_raw)) in
  cur_mp <- tmCurrentModPath tt ;;
  (* Step 4b: detect parametric-type applications in every index-type decl
     and from equality premise types, creating fresh monomorphic specialisations.
     E.g. [list nat] → fresh inductive [listnat] (npars = 0).
     The specialised types are then lifted to [listnat'] by the normal pipeline.
     [spec_kn_pairs] : list ((head_kn, [arg_kns]), spec_kn). *)
  let raw_ind_apps :=
    dedup_ind_apps
      ((flat_map (fun mwi =>
          flat_map (fun d => collect_ind_apps d.(decl_type)) (snd mwi))
        modes_with_idx)
       ++ ctor_eq_ind_apps_raw) in
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
  (* Step 5: initial lifting set = signature types + specialised parametric
     types (spec_kns), filtered to non-Prop / non-parametric.
     Equality-premise types are NOT in the initial lifting set; they act
     only as BFS seeds in Step 5b. *)
  let sig_kns :=
    dedup_kns (filter (fun kn => negb (existsb (eq_kername kn) rel_kns))
              arg_kns_raw) in
  type_kns <- monad_fold_left (fun acc kn =>
    mind <- tmQuoteInductive kn ;;
    if andb (negb (is_prop_mind mind)) (Nat.eqb mind.(ind_npars) 0)
    then tmReturn (List.app acc [kn])
    else tmReturn acc)
    (List.app sig_kns spec_kns) [] ;;
  (* BFS seeds from equality premises: non-Prop, non-parametric types not
     already in the initial lifting set. *)
  eq_seed_kns <- monad_fold_left (fun acc kn =>
    if existsb (eq_kername kn) type_kns then tmReturn acc
    else
      mind <- tmQuoteInductive kn ;;
      if andb (negb (is_prop_mind mind)) (Nat.eqb mind.(ind_npars) 0)
      then tmReturn (List.app acc [kn])
      else tmReturn acc)
    (dedup_kns (filter (fun kn => negb (existsb (eq_kername kn) rel_kns))
               ctor_eq_kns_raw)) [] ;;
  (* Step 5b: dependency closure — BFS from signature types AND equality
     seeds, but only add a type to the lifting set if it has at least one
     constructor argument type already in the lifting set. *)
  type_kns <- expand_dep_closure (type_kns ++ eq_seed_kns) type_kns [] rel_kns 200 ;;
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
Set Universe Checking.


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
          let nm' :=
            match binder_name d.(decl_name) with
            | nNamed _ => d.(decl_name)
            | nAnon    =>
              {| binder_name     := nNamed ("v" ++ string_of_nat (List.length (snd da)));
                 binder_relevance := binder_relevance d.(decl_name) |}
            end in
          (S (fst da), List.app (snd da)
            [{| decl_name := nm';
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

(* ================================================================== *)
(** ** Lift function generation                                        *)
(* ================================================================== *)

(** Classify a constructor arg type for a standalone original type
    (1 body, 0 params) at snoc position [snoc_i].
    Returns:
      None           = unrelated, pass through as identity
      Some None      = self-reference, apply recursive call
      Some (Some kn) = other lifted type [kn], call [snd kn ++ "Lift"] *)
Definition lift_arg_class
    (old_kn   : kername)
    (n_args   : nat)
    (snoc_i   : nat)
    (type_map : list (kername * inductive))
    (t        : term) : option (option kername) :=
  match t with
  | tRel n =>
    (* In a standalone type's cstr_args telescope (snoc order), the type of the
       arg at snoc_i is in a context where the (n_args-1-snoc_i) more-outer args
       are already bound (at tRel 0..n_args-2-snoc_i), so the mind body is at
       tRel (n_args-1-snoc_i).  That is the self-reference index. *)
    if Nat.eqb n (n_args - 1 - snoc_i) then Some None else None
  | tInd ind _ =>
    let kn := inductive_mind ind in
    if eq_kername kn old_kn then Some None
    else if existsb (fun p => eq_kername (fst p) kn) type_map
         then Some (Some kn)
         else None
  | _ => None
  end.

(** Build the tFix/tCoFix [def term] entry for the lift function of
    [old_kn] (body 0, described by [oib]) mapping to [new_ind].
    De Bruijn inside a branch with [n_args] args:
      tRel snoc_i      = constructor arg at snoc position [snoc_i]
      tRel n_args      = outer lambda variable (the scrutinee)
      tRel (n_args+1)  = the fix/cofix function itself
    [orig_form] is [Some (head_kn, arg_kns)] when [old_kn] is a
    specialization of a parametric type [head_kn] applied to [arg_kns];
    in that case the lift function takes [head_kn arg_kns...] as input
    rather than the intermediate specialized type [old_kn]. *)
Definition make_lift_def
    (old_kn    : kername)
    (oib       : one_inductive_body)
    (new_ind   : inductive)
    (type_map  : list (kername * inductive))
    (cur_mp    : modpath)
    (orig_form : option (kername * list kername))
    : def term :=
  let old_ind  := {| inductive_mind := old_kn; inductive_ind := 0 |} in
  (* Determine the case-expression's inductive, npar, params, and input type. *)
  let case_ind  :=
    match orig_form with
    | None              => old_ind
    | Some (head_kn, _) => {| inductive_mind := head_kn; inductive_ind := 0 |}
    end in
  let n_par    :=
    match orig_form with None => 0 | Some (_, aks) => List.length aks end in
  let par_terms :=
    match orig_form with
    | None              => []
    | Some (_, arg_kns) =>
      List.map (fun kn => tInd {| inductive_mind := kn; inductive_ind := 0 |} []) arg_kns
    end in
  let old_type :=
    match orig_form with
    | None      => tInd old_ind []
    | Some _    => match par_terms with
                   | [] => tInd case_ind []
                   | _  => tApp (tInd case_ind []) par_terms
                   end
    end in
  let new_type := tInd new_ind [] in
  let branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      (* Compute lifted args in snoc order, then reverse to constructor order *)
      let lifted_snoc :=
        List.map (fun snoc_i =>
          let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                       | Some d => d.(decl_type) | None => tVar "?" end in
          match lift_arg_class old_kn n_args snoc_i type_map arg_t with
          | Some None =>
            tApp (tRel (n_args + 1)) [tRel snoc_i]
          | Some (Some kn) =>
            tApp (tConst (cur_mp, snd kn ++ "Lift") []) [tRel snoc_i]
          | None =>
            tRel snoc_i
          end)
        (seq 0 n_args) in
      let lifted_args := List.rev lifted_snoc in
      let bbody := match lifted_args with
                   | [] => tConstruct new_ind ctor_idx []
                   | _  => tApp (tConstruct new_ind ctor_idx []) lifted_args
                   end in
      (* bcontext must be outermost-first = reverse of snoc-order cstr_args *)
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    oib.(ind_ctors) in
  let pred := {| puinst := []; pparams := par_terms;
                 pcontext := [{| binder_name := nAnon; binder_relevance := Relevant |}];
                 preturn  := new_type |} in
  let ci   := {| ci_ind := case_ind; ci_npar := n_par; ci_relevance := Relevant |} in
  let dbody :=
    tLambda {| binder_name := nAnon; binder_relevance := Relevant |} old_type
      (tCase ci pred (tRel 0) branches) in
  {| dname := {| binder_name := nNamed (snd old_kn ++ "Lift");
                 binder_relevance := Relevant |};
     dtype  := tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                     old_type new_type;
     dbody  := dbody;
     rarg   := 0 |}.

(** Declare a lift function for each type in [type_mapping] (in order, so
    dependencies come first).  Each [old_nm ++ "Lift"] maps original
    constructors to the corresponding lifted constructors.
    CoInductive types get tCoFix; Inductive types get tFix.
    If [old_kn] is a specialization of a parametric type recorded in
    [app_kn_map], the lift function takes the original parametric application
    as input (e.g. [list nat -> listnat']) rather than the intermediate
    specialized type. *)
Polymorphic Fixpoint generate_lift_fns
    (todo        : list (kername * inductive))
    (all_map     : list (kername * inductive))
    (app_kn_map  : list (kername * list kername * inductive))
    (cur_mp      : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let old_kn  := fst entry in
    let new_ind := snd entry in
    (* Check whether new_ind appears in app_kn_map, meaning old_kn is a
       specialization of a parametric type. *)
    let orig_form :=
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 app_kn_map with
      | Some e => Some (fst (fst e), snd (fst e))
      | None   => None
      end in
    tmBind (tmQuoteInductive old_kn) (fun old_mind =>
    tmBind (match nth_error old_mind.(ind_bodies) 0 with
            | None => tmFail ("generate_lift_fns: no body for " ++ snd old_kn)
            | Some oib =>
              let is_coind :=
                match old_mind.(ind_finite) with CoFinite => true | _ => false end in
              let d := make_lift_def old_kn oib new_ind all_map cur_mp orig_form in
              let fn_term := if is_coind then tCoFix [d] 0 else tFix [d] 0 in
              tmMkDefinition (snd old_kn ++ "Lift") fn_term
            end) (fun _ =>
    generate_lift_fns rest all_map app_kn_map cur_mp))
  end.

(* ------------------------------------------------------------------ *)
(** ** fnSymb parameter generation                                   *)
(* ------------------------------------------------------------------ *)

(** Map a single lifted inductive back to its old-type term.
    Parametric specialisations map to the applied form, e.g.
    [listnat' → list nat]. *)
Definition subst_ind_to_old
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list kername * inductive))
    (ind : inductive) : term :=
  match find (fun e =>
                andb (eq_kername (inductive_mind (snd e)) (inductive_mind ind))
                     (Nat.eqb (inductive_ind (snd e)) (inductive_ind ind)))
             type_map with
  | None => tInd ind []
  | Some (old_kn, _) =>
    let old_ind := {| inductive_mind := old_kn; inductive_ind := 0 |} in
    match find (fun e =>
                  andb (eq_kername (inductive_mind (snd e)) (inductive_mind ind))
                       (Nat.eqb (inductive_ind (snd e)) (inductive_ind ind)))
               app_kn_map with
    | Some e =>
      let head_ind  := {| inductive_mind := fst (fst e); inductive_ind := 0 |} in
      let par_terms :=
        List.map (fun kn => tInd {| inductive_mind := kn; inductive_ind := 0 |} [])
                 (snd (fst e)) in
      match par_terms with
      | [] => tInd head_ind []
      | _  => tApp (tInd head_ind []) par_terms
      end
    | None => tInd old_ind []
    end
  end.

(** Substitute [tInd] and [tRel]-encoded mutual-block body refs back to old
    types, given the current binder [depth] in the [cstr_type]/[cstr_args]
    telescope.
    In the mutual block with [n_bodies] bodies, body [j] appears as
    [tRel (depth + n_bodies - 1 - j)] at that depth. *)
Fixpoint subst_to_old_at_depth
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list kername * inductive))
    (block_kn   : kername)
    (n_bodies   : nat)
    (depth      : nat)
    (t          : term) : term :=
  let sub d := subst_to_old_at_depth type_map app_kn_map block_kn n_bodies d in
  match t with
  | tInd ind _ =>
    subst_ind_to_old type_map app_kn_map ind
  | tRel k =>
    (* Check whether k encodes a block-body reference at this depth.
       body j is at tRel (depth + n_bodies - 1 - j), valid for j in [0, n_bodies). *)
    if andb (Nat.leb depth k) (Nat.ltb k (depth + n_bodies)) then
      let j := (depth + n_bodies - 1) - k in
      subst_ind_to_old type_map app_kn_map
        {| inductive_mind := block_kn; inductive_ind := j |}
    else
      tRel k
  | tApp f args =>
    tApp (sub depth f) (List.map (sub depth) args)
  | tProd nm ty body =>
    tProd nm (sub depth ty) (sub (S depth) body)
  | _ => t
  end.

(** Build the raw type term for the fnSymb parameter of extra constructor
    [ctor] belonging to body [new_ind] in a block with [n_bodies] bodies and
    [n_params] parameters.
    For snoc-position [snoc_i], the binder depth in the [cstr_type] tProd
    chain is [n_params + n_args - 1 - snoc_i]. *)
Definition make_fnSymb_type
    (new_ind    : inductive)
    (n_bodies   : nat)
    (n_params   : nat)
    (ctor       : constructor_body)
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list kername * inductive))
    : term :=
  let block_kn := inductive_mind new_ind in
  let n_args   := ctor.(cstr_arity) in
  let sub_at   := subst_to_old_at_depth type_map app_kn_map block_kn n_bodies in
  let ret := sub_at (n_params + n_args) (tInd new_ind []) in
  (* Build (nm, old_type) pairs in snoc order, then reverse for declaration order *)
  let arg_pairs :=
    mapi (fun snoc_i d =>
      (d.(decl_name), sub_at (n_params + n_args - 1 - snoc_i) d.(decl_type)))
    ctor.(cstr_args) in
  List.fold_right
    (fun '(nm, ty) acc => tProd nm ty acc)
    ret
    (List.rev arg_pairs).

(** Declare a Coq Parameter (axiom) whose type is given as a raw MetaRocq term.
    [tmUnquoteTyped Type ty] converts the raw type term to a Coq [Type] value,
    which [tmAxiomRed] then uses to declare the axiom. *)
Definition tmMkParameter (id : ident) (ty : term) : TemplateMonad unit :=
  tmBind (tmUnquoteTyped Type ty) (fun T =>
  tmBind (tmAxiomRed id None T) (fun _ =>
  tmReturn tt)).

(** For each entry in [todo], declare a [<ctor>fnSymb] parameter for every
    constructor added to the lifted type beyond the original constructors.
    The parameter type is the constructor's function type with each lifted
    inductive substituted back to the corresponding old type. *)
Polymorphic Fixpoint generate_fnSymb_params
    (todo        : list (kername * inductive))
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list kername * inductive))
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let old_kn  := fst entry in
    let new_ind := snd entry in
    tmBind (tmQuoteInductive old_kn) (fun old_mind =>
    let n_old_ctors :=
      match nth_error old_mind.(ind_bodies) 0 with
      | None    => 0
      | Some ob => List.length ob.(ind_ctors)
      end in
    tmBind (tmQuoteInductive (inductive_mind new_ind)) (fun new_mind =>
    let n_bodies := List.length new_mind.(ind_bodies) in
    let n_params := new_mind.(ind_npars) in
    tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
            | None     => tmReturn tt
            | Some nob =>
              let extra := List.skipn n_old_ctors nob.(ind_ctors) in
              List.fold_left
                (fun acc c =>
                   tmBind acc (fun _ =>
                   tmMkParameter (c.(cstr_name) ++ "fnSymb")
                                 (make_fnSymb_type new_ind n_bodies n_params
                                                  c type_map app_kn_map)))
                extra (tmReturn tt)
            end) (fun _ =>
    generate_fnSymb_params rest type_map app_kn_map)))
  end.

(* ================================================================== *)
(** ** Rest function generation                                        *)
(* ================================================================== *)

(** Extract the first [n] argument types from a [tProd]-chain,
    skipping [skip] leading binders (parameters). *)
Fixpoint extract_arg_types (skip n : nat) (t : term) : list term :=
  match skip with
  | S k => match t with
            | tProd _ _ body => extract_arg_types k n body
            | _ => []
            end
  | 0 =>
    match n, t with
    | 0, _            => []
    | _, tSort _      => []
    | S k, tProd _ ty body => ty :: extract_arg_types 0 k body
    | _, _ => []
    end
  end.

(** Get the inductive reference from a type term ([tInd] or
    [tApp (tInd _ _) _]). *)
Definition ind_of_type (t : term) : option inductive :=
  match t with
  | tInd ind _           => Some ind
  | tApp (tInd ind _) _  => Some ind
  | _                    => None
  end.

(** Build a right-associative product type [T0 * (T1 * (... * T_{n-1}))].
    Singleton: returns [T0] unchanged. *)
Fixpoint make_prod_type (prod_kn : kername) (tys : list term) : term :=
  let prod_ind := {| inductive_mind := prod_kn; inductive_ind := 0 |} in
  match tys with
  | []        => tVar "make_prod_type:empty"
  | [t]       => t
  | t :: rest => tApp (tInd prod_ind []) [t; make_prod_type prod_kn rest]
  end.

(** Build a right-associative pair value [(v0, (v1, ...))] given parallel
    lists of types and values. Singleton: returns [v0] unchanged. *)
Fixpoint build_pair_term (prod_kn : kername) (tys vals : list term) : term :=
  let prod_ind := {| inductive_mind := prod_kn; inductive_ind := 0 |} in
  match tys, vals with
  | [_], [v]       => v
  | t :: rt, v :: rv =>
    tApp (tConstruct prod_ind 0 [])
         [t; make_prod_type prod_kn rt; v; build_pair_term prod_kn rt rv]
  | _, _ => tVar "build_pair_term:mismatch"
  end.

(** Build [n_in - 1] nested [match p with (a, b) => ...] case expressions
    to destructure the right-associative input pair.
    The scrutinee at each level is always [tRel 0] (the current pair).
    [out_type] is the overall return type used in each [preturn]. *)
Fixpoint build_nested_cases
    (prod_kn  : kername)
    (in_types : list term)
    (out_type : term)
    : term -> term :=
  let prod_ind := {| inductive_mind := prod_kn; inductive_ind := 0 |} in
  let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
  match in_types with
  | [] => fun body => body
  | [_] => fun body => body
  | T0 :: rest =>
    let rest_type := make_prod_type prod_kn rest in
    let ci   := {| ci_ind := prod_ind; ci_npar := 2; ci_relevance := Relevant |} in
    let pred := {| puinst   := [];
                   pparams  := [T0; rest_type];
                   pcontext := [anon_b];
                   preturn  := out_type |} in
    let inner := build_nested_cases prod_kn rest out_type in
    fun body =>
      tCase ci pred (tRel 0)
        [{| bcontext := [anon_b; anon_b];
            bbody    := inner body |}]
  end.

(** De Bruijn index for the [i]-th input (0-based) inside the innermost
    branch, after all [n_in - 1] pair destructions have added binders.
    Each match level binds 2 variables; the last input is always [tRel 0]
    (the rightmost leaf of the right-associative nest). *)
Definition input_var (i n_in : nat) : term :=
  if Nat.eqb i (n_in - 1) then tRel 0
  else tRel (2 * (n_in - 1 - i) - 1).

(** Build the raw term for [R'Rest]:
    a function taking the (possibly paired) input lifted types and
    returning the (possibly paired) output by applying the extra [An]
    constructor at each output position to all inputs. *)
Definition make_rest_term
    (prod_kn   : kername)
    (in_types  : list term)
    (out_types : list term)
    (out_ctors : list (inductive * nat))
    : term :=
  let n_in       := List.length in_types in
  let in_type    := match in_types  with [t] => t | _ => make_prod_type prod_kn in_types  end in
  let out_type_t := match out_types with [t] => t | _ => make_prod_type prod_kn out_types end in
  let in_vars    := mapi (fun i _ => input_var i n_in) in_types in
  let anon_b    := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let ctor_apps :=
    List.map (fun oc =>
      let out_ind  := fst oc in
      let ctor_idx := snd oc in
      match in_vars with
      | [] => tConstruct out_ind ctor_idx []
      | _  => tApp (tConstruct out_ind ctor_idx []) in_vars
      end)
    out_ctors in
  let body_inner :=
    match ctor_apps with
    | [app] =>
      match out_types with
      | [_] => app
      | _   => build_pair_term prod_kn out_types ctor_apps
      end
    | _ => build_pair_term prod_kn out_types ctor_apps
    end in
  let body :=
    match in_types with
    | []  => body_inner
    | [_] => body_inner
    | _   => build_nested_cases prod_kn in_types out_type_t body_inner
    end in
  tLambda anon_b in_type body.

(** Resolve the [(lifted_ind, ctor_idx)] for the extra [<rel>An<p>]
    constructor at output position [p], given the type term at that
    position from the lifted relation's [ind_type]. *)
Definition get_out_ctor
    (rel_name : string)
    (p        : nat)
    (out_type : term)
    : TemplateMonad (inductive * nat) :=
  match ind_of_type out_type with
  | None =>
    tmFail ("get_out_ctor: no inductive at position " ++ string_of_nat p)
  | Some out_ind =>
    tmBind (tmQuoteInductive (inductive_mind out_ind)) (fun out_mind =>
    let ctor_nm := rel_name ++ "An" ++ string_of_nat p in
    match nth_error out_mind.(ind_bodies) (inductive_ind out_ind) with
    | None =>
      tmFail ("get_out_ctor: no body at index " ++ string_of_nat (inductive_ind out_ind))
    | Some out_oib =>
      let idx :=
        match find_ctor_idx ctor_nm out_oib.(ind_ctors) 0 with
        | Some i => i
        | None   => 0
        end in
      tmReturn (out_ind, idx)
    end)
  end.

(** For each entry in [todo], declare [[rel_name]'Rest]: a function that
    takes the (possibly paired) lifted input types and applies the extra
    [An] constructor for each output position, producing a (possibly
    paired) output.  The lifted relations must already exist in the
    global environment when this is called. *)
Polymorphic Fixpoint generate_rest_fns
    (todo    : list (kername * (string * (list nat * list nat))))
    (cur_mp  : modpath)
    (prod_kn : kername)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | (block_kn, (rel_name, (in_pos, out_pos))) :: rest_todo =>
    (* The lifted block is registered under snd(block_kn) ++ prime,
       so we quote that block and then search for the body by name. *)
    let lifted_block_kn := (cur_mp, snd block_kn ++ "'") in
    let lifted_nm       := rel_name ++ "'" in
    tmBind (tmQuoteInductive lifted_block_kn) (fun new_mind =>
    let n_params := new_mind.(ind_npars) in
    let n_total  := List.length in_pos + List.length out_pos in
    match find (fun ob => String.eqb ob.(ind_name) lifted_nm)
               new_mind.(ind_bodies) with
    | None =>
      tmFail ("generate_rest_fns: cannot find body " ++ lifted_nm)
    | Some oib =>
      let all_types := extract_arg_types n_params n_total oib.(ind_type) in
      let in_types  := List.map (fun p => nth p all_types (tVar "?")) in_pos in
      let out_types := List.map (fun p => nth p all_types (tVar "?")) out_pos in
      tmBind (monad_map (fun p =>
                get_out_ctor rel_name p (nth p all_types (tVar "?")))
              out_pos)
      (fun out_ctors =>
      let fn_term := make_rest_term prod_kn in_types out_types out_ctors in
      tmBind (tmMkDefinition (rel_name ++ "'Rest") fn_term) (fun _ =>
      generate_rest_fns rest_todo cur_mp prod_kn))
    end)
  end.

(** For each co-inductive type in [todo], declare:
    - [Parameter undefined<TypeName> : <OriginalType>]
    - [Parameter <TypeName>PushSymbol : <LiftedType> -> <OriginalType>]
    Inductive (non-coinductive) types are silently skipped. *)
Polymorphic Fixpoint generate_push_params
    (todo       : list (kername * inductive))
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list kername * inductive))
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let old_kn  := fst entry in
    let new_ind := snd entry in
    tmBind (tmQuoteInductive old_kn) (fun old_mind =>
    let is_coind :=
      match old_mind.(ind_finite) with CoFinite => true | _ => false end in
    let type_nm  := snd old_kn in
    let old_type := subst_ind_to_old type_map app_kn_map new_ind in
    let new_type := tInd new_ind [] in
    tmBind (tmMkParameter ("undefined" ++ type_nm) old_type) (fun _ =>
    tmBind (if negb is_coind then tmReturn tt
            else
              let push_ty  :=
                tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                      new_type old_type in
              tmMkParameter (type_nm ++ "PushSymbol") push_ty)
    (fun _ =>
    generate_push_params rest type_map app_kn_map)))
  end.

(* ------------------------------------------------------------------ *)
(** ** Push function generation                                        *)
(* ------------------------------------------------------------------ *)

(** Classify a constructor arg type from a LIFTED inductive's constructor.
    [new_kn]   : the mutual block kername (inductive_mind new_ind)
    [n_block]  : number of bodies in that block
    [body_idx] : index of the current body (inductive_ind new_ind)
    In a block with [n_block] bodies, body [j]'s self-ref at arg depth [d]
    is [tRel(d + n_block - 1 - j)].  We invert this to identify block refs.
    Returns:
    - [Some None]       : self-reference → apply the push fixpoint recursively
    - [Some (Some kn)]  : cross-block ref with original kername [kn] → [kn ++ "Push"]
    - [None]            : unrelated type → pass through as identity *)
Definition push_arg_class
    (new_kn   : kername)
    (n_block  : nat)
    (body_idx : nat)
    (type_map : list (kername * inductive))
    (n_args   : nat)
    (snoc_i   : nat)
    (t        : term) : option (option kername) :=
  let depth := n_args - 1 - snoc_i in
  match t with
  | tRel n =>
    if andb (Nat.leb depth n) (Nat.ltb (n - depth) n_block) then
      let j := n_block - 1 - (n - depth) in
      if Nat.eqb j body_idx then Some None
      else
        match find (fun e =>
                      andb (eq_kername (inductive_mind (snd e)) new_kn)
                           (Nat.eqb (inductive_ind (snd e)) j))
                   type_map with
        | Some (old_kn, _) => Some (Some old_kn)
        | None             => None
        end
    else None
  | tInd ind _ =>
    let kn := inductive_mind ind in
    let j  := inductive_ind ind in
    if andb (eq_kername kn new_kn) (Nat.eqb j body_idx) then Some None
    else
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) kn)
                         (Nat.eqb (inductive_ind (snd e)) j))
                 type_map with
      | Some (old_kn, _) => Some (Some old_kn)
      | None             => None
      end
  | _ => None
  end.

(** Build the [def term] entry for the push function of [old_kn] mapping
    the lifted inductive [new_ind] (body [new_oib] in a block with [n_block]
    bodies) back to the original type.
    For parametric specialisations (e.g. [listnat] is [list nat]), the return
    type and constructor heads use the parametric head ([list]) with params
    applied, mirroring [make_lift_def]'s [orig_form] logic.
    De Bruijn inside a branch with [n_args] args:
      tRel snoc_i     = constructor arg at snoc position [snoc_i]
      tRel n_args     = outer lambda variable (the scrutinee, unused)
      tRel (n_args+1) = the fix/cofix function itself (self-push) *)
Definition make_push_def
    (old_kn      : kername)
    (new_ind     : inductive)
    (n_block     : nat)
    (new_oib     : one_inductive_body)
    (n_old_ctors : nat)
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list kername * inductive))
    (cur_mp      : modpath)
    : def term :=
  (* Detect parametric specialisation: is new_ind in app_kn_map? *)
  let orig_form :=
    match find (fun e =>
                  andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                       (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
               app_kn_map with
    | Some e => Some (fst (fst e), snd (fst e))
    | None   => None
    end in
  let head_ind :=
    match orig_form with
    | None              => {| inductive_mind := old_kn; inductive_ind := 0 |}
    | Some (head_kn, _) => {| inductive_mind := head_kn; inductive_ind := 0 |}
    end in
  let par_terms :=
    match orig_form with
    | None              => []
    | Some (_, arg_kns) =>
      List.map (fun kn => tInd {| inductive_mind := kn; inductive_ind := 0 |} []) arg_kns
    end in
  let old_type :=
    match par_terms with
    | [] => tInd head_ind []
    | _  => tApp (tInd head_ind []) par_terms
    end in
  let new_type     := tInd new_ind [] in
  let type_nm      := snd old_kn in
  let new_kn       := inductive_mind new_ind in
  let body_idx     := inductive_ind new_ind in
  let undefinedConst := tConst (cur_mp, "undefined" ++ type_nm) [] in
  let anon_b       := {| binder_name := nAnon; binder_relevance := Relevant |} in
  (* All push functions use a nat depth parameter d:
       fix f (d : nat) (s' : new_type) : old_type :=
         match d with 0 => undefinedT | S m => match s' with ... end end
     De Bruijn inside inner case branches (n_args branch binders):
       tRel 0..n_args-1 = branch binders (snoc order)
       tRel n_args       = m  (S-branch binder)
       tRel (n_args+1)   = s' (second lambda)
       tRel (n_args+2)   = d  (first lambda)
       tRel (n_args+3)   = the fix itself
     Self-recursive call:      tApp fix [m; sub_arg]
     External push call:       tApp pushConst [m; arg]  *)
  let branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      let bbody :=
        if Nat.ltb ctor_idx n_old_ctors then
          let pushed_snoc :=
            List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
              | Some None =>
                  tApp (tRel (n_args + 3)) [tRel n_args; tRel snoc_i]
              | Some (Some kn) =>
                  let push_const := tConst (cur_mp, snd kn ++ "Push") [] in
                  tApp push_const [tRel n_args; tRel snoc_i]
              | None => tRel snoc_i
              end)
            (seq 0 n_args) in
          let pushed_args := List.rev pushed_snoc in
          let all_args := List.app par_terms pushed_args in
          match all_args with
          | [] => tConstruct head_ind ctor_idx []
          | _  => tApp (tConstruct head_ind ctor_idx []) all_args
          end
        else
          undefinedConst
      in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    new_oib.(ind_ctors) in
  let pred  := {| puinst := []; pparams := [];
                  pcontext := [anon_b];
                  preturn  := old_type |} in
  let ci    := {| ci_ind := new_ind; ci_npar := 0; ci_relevance := Relevant |} in
  (* fix f (d : nat) (s' : new_type) : old_type :=
       match d with 0 => undefinedT | S m => match s' with ... end end *)
  let nat_ind_ref := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
  let nat_ci   := {| ci_ind := nat_ind_ref; ci_npar := 0; ci_relevance := Relevant |} in
  let nat_pred := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := old_type |} in
  let inner_case := tCase ci pred (tRel 1) branches in
  let o_branch   := {| bcontext := [];       bbody := undefinedConst |} in
  let s_branch   := {| bcontext := [anon_b]; bbody := inner_case     |} in
  let dbody :=
    tLambda anon_b (tInd nat_ind_ref [])
      (tLambda anon_b new_type
        (tCase nat_ci nat_pred (tRel 1) [o_branch; s_branch])) in
  {| dname := {| binder_name := nNamed (type_nm ++ "Push"); binder_relevance := Relevant |};
     dtype  := tProd anon_b (tInd nat_ind_ref []) (tProd anon_b new_type old_type);
     dbody  := dbody;
     rarg   := 0 |}.

(** Declare a push function for every type in [todo].
    All push functions use [tFix] on a leading [nat] depth parameter:
    at depth 0 they return [undefined<T>]; at depth [S m] they match on
    the lifted constructor, recursing with [m] for sub-values of the same
    type, and returning [undefined<T>] for animation constructors. *)
Polymorphic Fixpoint generate_push_fns
    (todo        : list (kername * inductive))
    (all_map     : list (kername * inductive))
    (app_kn_map  : list (kername * list kername * inductive))
    (cur_mp      : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let old_kn  := fst entry in
    let new_ind := snd entry in
    tmBind (tmQuoteInductive old_kn) (fun old_mind =>
    tmBind (tmQuoteInductive (inductive_mind new_ind)) (fun new_mind =>
    tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
            | None =>
              tmFail ("generate_push_fns: no body for " ++ snd old_kn)
            | Some new_oib =>
              let n_old_ctors :=
                match nth_error old_mind.(ind_bodies) 0 with
                | Some ob => List.length ob.(ind_ctors)
                | None    => 0
                end in
              let n_block := List.length new_mind.(ind_bodies) in
              let d := make_push_def old_kn new_ind n_block new_oib n_old_ctors
                                     all_map app_kn_map cur_mp in
              tmMkDefinition (snd old_kn ++ "Push") (tFix [d] 0)
            end) (fun _ =>
    generate_push_fns rest all_map app_kn_map cur_mp)))
  end.

(* ------------------------------------------------------------------ *)
(** ** InputLift function generation                                  *)
(* ------------------------------------------------------------------ *)

(** Given an original type term, return [(lifted_type, Some lift_fn)] if
    the type is tracked in [type_map]/[app_kn_map], or [(t, None)] if not. *)
Definition classify_in_type
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list kername * inductive))
    (cur_mp     : modpath)
    (t          : term)
    : term * option term :=
  match t with
  | tInd ind _ =>
    let kn := inductive_mind ind in
    match find (fun e => eq_kername (fst e) kn) type_map with
    | Some (old_kn, new_ind) =>
      (tInd new_ind [], Some (tConst (cur_mp, snd old_kn ++ "Lift") []))
    | None => (t, None)
    end
  | tApp (tInd ind _) args =>
    let kn      := inductive_mind ind in
    let arg_kns := List.concat (List.map (fun a =>
      match a with tInd i _ => [inductive_mind i] | _ => [] end) args) in
    let found :=
      find (fun e =>
              andb (eq_kername (fst (fst e)) kn)
                   (andb (Nat.eqb #|arg_kns| #|snd (fst e)|)
                         (forallb (fun ab => eq_kername (fst ab) (snd ab))
                                  (combine arg_kns (snd (fst e))))))
           app_kn_map in
    match found with
    | Some (_, new_ind) =>
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 type_map with
      | Some (old_kn, _) =>
        (tInd new_ind [], Some (tConst (cur_mp, snd old_kn ++ "Lift") []))
      | None => (t, None)
      end
    | None => (t, None)
    end
  | _ => (t, None)
  end.

(** Build the raw term for [<rel_name>inputLift]:
      fun inp => match inp with
                 | Success v => Success lifted_out_type (apply lifts to v)
                 | _         => NoMatch lifted_out_type
                 end
    [in_types]     : original types at input positions (from original relation's ind_type)
    [lifted_types] : corresponding lifted types
    [lift_fns]     : [Some fn] to apply, or [None] for identity, per input *)
Definition make_inputLift_term
    (prod_kn      : kername)
    (anim_res_kn  : kername)
    (in_types     : list term)
    (lifted_types : list term)
    (lift_fns     : list (option term))
    : term :=
  let anim_res_ind  := {| inductive_mind := anim_res_kn; inductive_ind := 0 |} in
  let anon_b        := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let in_type       := match in_types     with [t] => t | _ => make_prod_type prod_kn in_types     end in
  let lifted_type   := match lifted_types with [t] => t | _ => make_prod_type prod_kn lifted_types end in
  let anim_in_type  := tApp (tInd anim_res_ind []) [in_type] in
  let anim_out_type := tApp (tInd anim_res_ind []) [lifted_type] in
  let n_in          := List.length in_types in
  let no_match_body := tApp (tConstruct anim_res_ind 2 []) [lifted_type] in
  (* Apply each lift function (or identity) to the corresponding input variable *)
  let lifted_vals :=
    mapi (fun i lf =>
      match lf with
      | Some fn => tApp fn [input_var i n_in]
      | None    => input_var i n_in
      end)
    lift_fns in
  let lifted_val    := build_pair_term prod_kn lifted_types lifted_vals in
  let success_inner := tApp (tConstruct anim_res_ind 1 []) [lifted_type; lifted_val] in
  (* For multiple inputs, destructure the nested pair before applying lifts *)
  let success_body  :=
    match in_types with
    | [] | [_] => success_inner
    | _        => build_nested_cases prod_kn in_types anim_out_type success_inner
    end in
  let case_expr :=
    tCase
      {| ci_ind := anim_res_ind; ci_npar := 1; ci_relevance := Relevant |}
      {| puinst := []; pparams := [in_type]; pcontext := [anon_b]; preturn := anim_out_type |}
      (tRel 0)
      [ {| bcontext := []; bbody := no_match_body |}         (* FuelError *)
      ; {| bcontext := [anon_b]; bbody := success_body |}    (* Success v *)
      ; {| bcontext := []; bbody := no_match_body |} ]       (* NoMatch *)
  in
  tLambda anon_b anim_in_type case_expr.

(** Declare [<rel_name>inputLift] for every entry in [kn_mode_list]. *)
Polymorphic Fixpoint generate_inputLift_fns
    (todo        : list (kername * (string * (list nat * list nat))))
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list kername * inductive))
    (prod_kn     : kername)
    (anim_res_kn : kername)
    (cur_mp      : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let block_kn := fst entry in
    let rel_name := fst (snd entry) in
    let in_pos   := fst (snd (snd entry)) in
    let out_pos  := snd (snd (snd entry)) in
    tmBind (tmQuoteInductive block_kn) (fun orig_mind =>
    match find (fun ob => String.eqb ob.(ind_name) rel_name) orig_mind.(ind_bodies) with
    | None => tmFail ("generate_inputLift_fns: cannot find body " ++ rel_name)
    | Some oib =>
      let n_params   := orig_mind.(ind_npars) in
      let n_total    := List.length in_pos + List.length out_pos in
      let all_types  := extract_arg_types n_params n_total oib.(ind_type) in
      let in_types   := List.map (fun p => nth p all_types (tVar "?")) in_pos in
      let classified := List.map (classify_in_type type_map app_kn_map cur_mp) in_types in
      let lifted_types := List.map fst classified in
      let lift_fns     := List.map snd classified in
      let fn_term := make_inputLift_term prod_kn anim_res_kn in_types lifted_types lift_fns in
      tmBind (tmMkDefinition (rel_name ++ "inputLift") fn_term) (fun _ =>
      generate_inputLift_fns rest type_map app_kn_map prod_kn anim_res_kn cur_mp)
    end)
  end.

(* ------------------------------------------------------------------ *)
(** ** OutputPush function generation                                  *)
(* ------------------------------------------------------------------ *)

(** Given an original output type term, return [(lifted_type, Some push_fn, is_coind_push)]
    if the type is tracked in [type_map]/[app_kn_map], or [(t, None, false)] if not.
    [is_coind_push] is true when the push function takes an extra [nat] depth argument. *)
Definition classify_out_type
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list kername * inductive))
    (cur_mp     : modpath)
    (t          : term)
    : term * option term :=
  match t with
  | tInd ind _ =>
    let kn := inductive_mind ind in
    match find (fun e => eq_kername (fst e) kn) type_map with
    | Some (old_kn, new_ind) =>
      (tInd new_ind [], Some (tConst (cur_mp, snd old_kn ++ "Push") []))
    | None => (t, None)
    end
  | tApp (tInd ind _) args =>
    let kn      := inductive_mind ind in
    let arg_kns := List.concat (List.map (fun a =>
      match a with tInd i _ => [inductive_mind i] | _ => [] end) args) in
    let found :=
      find (fun e =>
              andb (eq_kername (fst (fst e)) kn)
                   (andb (Nat.eqb #|arg_kns| #|snd (fst e)|)
                         (forallb (fun ab => eq_kername (fst ab) (snd ab))
                                  (combine arg_kns (snd (fst e))))))
           app_kn_map in
    match found with
    | Some (_, new_ind) =>
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 type_map with
      | Some (old_kn, _) =>
        (tInd new_ind [], Some (tConst (cur_mp, snd old_kn ++ "Push") []))
      | None => (t, None)
      end
    | None => (t, None)
    end
  | _ => (t, None)
  end.

(** Build the raw term for [<rel_name>outputPush]:
      fun (d : nat) out => match out with
                           | Success v => Success orig (apply pushes d to v)
                           | _         => NoMatch orig
                           end
    All push functions take a leading [nat] depth argument, so [d] is always
    threaded through to every push application.
    [orig_types]   : original types at output positions
    [lifted_types] : corresponding lifted types (input to this function)
    [push_fns]     : [Some fn] or [None] per output *)
Definition make_outputPush_term
    (prod_kn      : kername)
    (anim_res_kn  : kername)
    (orig_types   : list term)
    (lifted_types : list term)
    (push_fns     : list (option term))
    : term :=
  let anim_res_ind  := {| inductive_mind := anim_res_kn; inductive_ind := 0 |} in
  let nat_ind_ref   := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
  let anon_b        := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let lifted_type   := match lifted_types with [t] => t | _ => make_prod_type prod_kn lifted_types end in
  let orig_type     := match orig_types   with [t] => t | _ => make_prod_type prod_kn orig_types   end in
  let anim_in_type  := tApp (tInd anim_res_ind []) [lifted_type] in
  let anim_out_type := tApp (tInd anim_res_ind []) [orig_type] in
  let n_in          := List.length lifted_types in
  (* Depth variable inside the success branch body.
     Binder stack above the depth_var (inside the Success branch):
       1 (anim_res lambda) + 1 (Success branch binder) + 2*(n_in-1) (pair-match binders) = 2*n_in.
     For n_in=1: 1 + 1 = 2 = 2*1.  depth_var = tRel (2*n_in). *)
  let depth_var     := tRel (2 * n_in) in
  let no_match_body := tApp (tConstruct anim_res_ind 2 []) [orig_type] in
  let pushed_vals :=
    mapi (fun i pf =>
      match pf with
      | Some fn => tApp fn [depth_var; input_var i n_in]
      | None    => input_var i n_in
      end)
    push_fns in
  let pushed_val    := build_pair_term prod_kn orig_types pushed_vals in
  let success_inner := tApp (tConstruct anim_res_ind 1 []) [orig_type; pushed_val] in
  let success_body  :=
    match lifted_types with
    | [] | [_] => success_inner
    | _        => build_nested_cases prod_kn lifted_types anim_out_type success_inner
    end in
  let case_expr :=
    tCase
      {| ci_ind := anim_res_ind; ci_npar := 1; ci_relevance := Relevant |}
      {| puinst := []; pparams := [lifted_type]; pcontext := [anon_b]; preturn := anim_out_type |}
      (tRel 0)
      [ {| bcontext := []; bbody := no_match_body |}
      ; {| bcontext := [anon_b]; bbody := success_body |}
      ; {| bcontext := []; bbody := no_match_body |} ]
  in
  let fn_body := tLambda anon_b anim_in_type case_expr in
  tLambda anon_b (tInd nat_ind_ref []) fn_body.

(** Declare [<rel_name>outputPush] for every entry in [kn_mode_list].
    Every generated function takes a leading [nat] depth argument and passes it
    to each push function applied to an output value. *)
Polymorphic Fixpoint generate_outputPush_fns
    (todo        : list (kername * (string * (list nat * list nat))))
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list kername * inductive))
    (prod_kn     : kername)
    (anim_res_kn : kername)
    (cur_mp      : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let block_kn := fst entry in
    let rel_name := fst (snd entry) in
    let in_pos   := fst (snd (snd entry)) in
    let out_pos  := snd (snd (snd entry)) in
    tmBind (tmQuoteInductive block_kn) (fun orig_mind =>
    match find (fun ob => String.eqb ob.(ind_name) rel_name) orig_mind.(ind_bodies) with
    | None => tmFail ("generate_outputPush_fns: cannot find body " ++ rel_name)
    | Some oib =>
      let n_params   := orig_mind.(ind_npars) in
      let n_total    := List.length in_pos + List.length out_pos in
      let all_types  := extract_arg_types n_params n_total oib.(ind_type) in
      let orig_types := List.map (fun p => nth p all_types (tVar "?")) out_pos in
      let classified   := List.map (classify_out_type type_map app_kn_map cur_mp) orig_types in
      let lifted_types := List.map fst classified in
      let push_fns     := List.map snd classified in
      let fn_term := make_outputPush_term prod_kn anim_res_kn orig_types lifted_types push_fns in
      tmBind (tmMkDefinition (rel_name ++ "outputPush") fn_term) (fun _ =>
      generate_outputPush_fns rest type_map app_kn_map prod_kn anim_res_kn cur_mp)
    end)
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
Unset Universe Checking.
Polymorphic Definition lift_coinductive_relation
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
    _ <- generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp ;;
    _ <- generate_fnSymb_params type_mapping type_mapping app_kn_mapping ;;
    _ <- monad_fold_left (fun _ block_kn =>
      let block_modes :=
        List.map snd (filter (fun p => eq_kername (fst p) block_kn) kn_mode_list) in
      lift_relation block_kn rel_mapping type_mapping app_kn_mapping block_modes)
      unique_block_kns tt ;;
    prod_refs <- tmLocate "prod" ;;
    anim_refs <- tmLocate "animation_result" ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) prod_refs,
          find (fun g => match g with IndRef _ => true | _ => false end) anim_refs with
    | Some (IndRef prod_ind), Some (IndRef anim_ind) =>
      let prod_kn     := inductive_mind prod_ind in
      let anim_res_kn := inductive_mind anim_ind in
      tmBind (generate_inputLift_fns kn_mode_list type_mapping app_kn_mapping
                                     prod_kn anim_res_kn cur_mp) (fun _ =>
      tmBind (generate_rest_fns kn_mode_list cur_mp prod_kn) (fun _ =>
      tmBind (generate_push_params type_mapping type_mapping app_kn_mapping) (fun _ =>
      tmBind (generate_push_fns type_mapping type_mapping app_kn_mapping cur_mp) (fun _ =>
      generate_outputPush_fns kn_mode_list type_mapping app_kn_mapping
                              prod_kn anim_res_kn cur_mp))))
    | _, _ => @tmFail unit "lift_coinductive_relation: cannot locate prod or animation_result"
    end
  end.
Set Universe Checking.



(* ================================================================== *)
(** ** Composite entry point: lift + animate + wrap                   *)
(* ================================================================== *)

(** Combined entry point that:
    1. Lifts all relations (and their types) via [lift_coinductive_relation].
    2. Runs [animate_coinductive] on the lifted top relation.
    3. Builds a composite function named [rel_nm ++ "AnimatedTopFn"]:
         fun fuel depth inp =>
           <rel>outputPush depth (<rel>'AnimatedTopFn fuel (<rel>inputLift inp))
    All push functions take a depth argument, so the composite always does too. *)
Definition animate_coinductive_with_lift
    (rel_kn : kername)
    (modes  : mode_map)
    (fuel   : nat)
    : TemplateMonad unit :=
  let rel_nm := snd rel_kn in
  lift_coinductive_relation modes ;;
  cur_mp <- tmCurrentModPath tt ;;
  let lifted_kn    := (cur_mp, rel_nm ++ "'") in
  let lifted_modes := List.map (fun me => (fst me ++ "'", snd me)) modes in
  _ <- animate_coinductive lifted_kn lifted_modes fuel ;;
  top_mind <- tmQuoteInductive rel_kn ;;
  match find (fun me => String.eqb (fst me) rel_nm) modes,
        find (fun ob => String.eqb ob.(ind_name) rel_nm) top_mind.(ind_bodies) with
  | Some (_, (in_pos, out_pos)), Some top_oib =>
    let n_params  := top_mind.(ind_npars) in
    let n_total   := List.length in_pos + List.length out_pos in
    let all_types := extract_arg_types n_params n_total top_oib.(ind_type) in
    prod_refs <- tmLocate "prod" ;;
    anim_refs <- tmLocate "animation_result" ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) prod_refs,
          find (fun g => match g with IndRef _ => true | _ => false end) anim_refs with
    | Some (IndRef prod_ind), Some (IndRef anim_ind) =>
      let prod_kn      := inductive_mind prod_ind in
      let anim_res_kn  := inductive_mind anim_ind in
      let anim_res_ind := {| inductive_mind := anim_res_kn; inductive_ind := 0 |} in
      let nat_ind      := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
      let anon_b       := {| binder_name := nAnon; binder_relevance := Relevant |} in
      let in_types     := List.map (fun p => nth p all_types (tVar "?")) in_pos in
      let out_types    := List.map (fun p => nth p all_types (tVar "?")) out_pos in
      let in_type      := match in_types with [t] => t | _ => make_prod_type prod_kn in_types end in
      let anim_in_type := tApp (tInd anim_res_ind []) [in_type] in
      let inputLift_fn  := tConst (cur_mp, rel_nm ++ "inputLift") [] in
      let outputPush_fn := tConst (cur_mp, rel_nm ++ "outputPush") [] in
      let animFn        := tConst (cur_mp, rel_nm ++ "'" ++ top_fn_suffix) [] in
      (* All outputPush functions take a leading nat depth argument.
         We use the same value for both fuel and depth. *)
      let composite :=
        (* fun n inp => outputPush n (animFn n (inputLift inp)) *)
        tLambda anon_b (tInd nat_ind [])   (* n   = tRel 1 inside next lambda *)
        (tLambda anon_b anim_in_type       (* inp = tRel 0 *)
        (tApp outputPush_fn
          [tRel 1;                          (* n = depth *)
           tApp animFn [tRel 1; tApp inputLift_fn [tRel 0]]]))  (* n = fuel *)
      in
      tmMkDefinition (rel_nm ++ top_fn_suffix) composite
    | _, _ =>
      tmFail "animate_coinductive_with_lift: cannot locate prod or animation_result"
    end
  | None, _ => tmFail ("animate_coinductive_with_lift: no mode entry for " ++ rel_nm)
  | _, None  => tmFail ("animate_coinductive_with_lift: cannot find body " ++ rel_nm)
  end.
  
  
  
Set Universe Checking.  
Inductive myLst : Type :=
| nilmyLst : myLst
| SeqmyLst : nat -> myLst -> myLst.
  
Inductive listRel : nat -> nat -> Prop :=
| lRc : forall a b,  [a] = [b] -> listRel a b.  


  
MetaRocq Run (animate_coinductive_with_lift <?listRel?>
               [("listRel", ([0],   [1]))
                ]
               100). 
               
Print listRel'.


(*
(* ================================================================== *)
(** ** Example: all relations (single mutual block + separate blocks)  *)
(*                                                                      *)
(*  Integrate / addStm / addNat are declared with [with], so they      *)
(*  form one mutual inductive block.                                    *)
(*  isZero and Len are declared in two separate [Inductive] commands,  *)
(*  so lift_coinductive_relation must handle multiple blocks.           *)
(* ================================================================== *)



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
  
Inductive tripleIn : nat -> nat -> bool -> nat -> nat -> Prop :=
| tInC : forall a b c, tripleIn a b c a b.  

Unset Universe Checking.




                

MetaRocq Run (animate_coinductive_with_lift <?Integrate?>
               [("Integrate", ([0],   [1]));
                ("addStm",    ([0;1], [2]));
                ("addNat",    ([0;1], [2]))
                ]
               100).






Set Universe Checking.




Print IntegrateAnimatedTopFn.

CoFixpoint from (n : nat) : stream :=
Seq n (from (S n)).

Compute IntegrateAnimatedTopFn 25 (Success stream (from 0)). 

*)






(*
CoFixpoint streamPushTransparent (s' : stream')  : stream :=
match s' with
 | nil' => nil
 | Seq' n s => Seq (natPush n) (streamPushTransparent s)
 | IntegrateAn1 s => IntegrateAn1fnSymb (streamPushSymbol s)
 | addStmAn2 n s => addStmAn2fnSymb (natPush n) (streamPushSymbol s)
end. 
*)



(*
MetaRocq Run (animate_coinductive_with_lift <?Integrate?>
               [("Integrate", ([0],   [1]));
                ("addStm",    ([0;1], [2]));
                ("addNat",    ([0;1], [2]))
                ] 300).

Print IntegrateAnimatedTopFn.
Set Universe Checking.
CoFixpoint from (n : nat) : stream :=
Seq n (from (S n)).
CoFixpoint from' (n' : nat') : stream' :=
Seq' n' (from' (S' n')).

Fixpoint streamPushTransparent (s' : stream') (n : nat) : stream :=
match n with 
| 0 => streamPushSymbol s'
| S m => match s' with
         | nil' => nil
         | Seq' n s => Seq (natPush n) (streamPushTransparent s m)
         | IntegrateAn1 s => IntegrateAn1fnSymb (streamPushTransparent s m)
         | addStmAn2 n s => addStmAn2fnSymb (natPush n) (streamPushTransparent s m)
         end 
end. 

Fixpoint streamPushTransparent2 (s' : stream') (n : nat) : stream :=
match n with 
| 0 => undefinedstream
| S m => match s' with
         | nil' => nil
         | Seq' n s => Seq (natPush n) (streamPushTransparent2 s m)
         | IntegrateAn1 s => undefinedstream
         | addStmAn2 n s => undefinedstream
         end 
end. 

Print IntegrateAnimatedTopFn.
MetaRocq Run (res <- tmEval all (IntegrateAnimatedTopFn 10 (Success stream (from O )));; tmDefinition "res" res).

Compute streamPushTransparent2 (
            (Seq' O'
               (Seq' (S' O')
                  (Seq' (S' (S' (S' O')))
                     (Seq' (addNatAn2 (S' O') (addNatAn2 (S' (S' O')) (S' (S' (S' O')))))
                        (addStmAn2 O'
                           (addStmAn2 (S' O')
                              (addStmAn2 (S' (S' O'))
                                 (addStmAn2 (S' (S' (S' O')))
                                    (IntegrateAn1
                                       ((cofix Fcofix (x : stream) : stream' :=
                                           match x with
                                           | nil => nil'
                                           | Seq x0 x1 =>
                                               Seq'
                                                 ((fix Ffix (x2 : nat) : nat' :=
                                                     match x2 with
                                                     | 0 => O'
                                                     | S x3 => S' (Ffix x3)
                                                     end)
                                                    x0)
                                                 (Fcofix x1)
                                           end)
                                          ((cofix Fcofix (x : nat) : stream := Seq x (Fcofix (S x))) 4)))))))))))) 10.
   






Print res.

*) 


        
                
                
                
                
                
                
                
                
                
                
                
                
                
                
                
                
                              