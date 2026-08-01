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
Require Import Animation.HoleyResult.

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

(** True iff [t] is a "pure inductive type term":
    either [tInd ...] or [tApp (tInd ...) args] where every arg is also pure. *)
Fixpoint is_ind_type (t : term) : bool :=
  match t with
  | tInd _ _             => true
  | tApp (tInd _ _) args => forallb is_ind_type args
  | _                    => false
  end.

(** Canonical name for a pure inductive type term.
    Mirrors [spec_name] generation: head short-name concatenated with arg names. *)
Fixpoint ind_type_name (t : term) : string :=
  match t with
  | tInd ind _             => snd (inductive_mind ind)
  | tApp (tInd ind _) args =>
      fold_left (fun s a => s ++ ind_type_name a) args (snd (inductive_mind ind))
  | _                      => ""
  end.

(** Boolean equality of pure inductive type terms via canonical names. *)
Definition eqb_ind_type (t1 t2 : term) : bool :=
  String.eqb (ind_type_name t1) (ind_type_name t2).

(** Collect just the top-level [tApp (tInd head_kn _) args] from a type term
    (no recursion into the args).  Used for mode-position index types so that
    nested type arguments (e.g. [list nat] inside [prod (list nat) (list nat)])
    do NOT independently enter the specialisation set. *)
Definition collect_ind_apps_toplevel (t : term) : list (kername * list term) :=
  match t with
  | tApp (tInd head _) args =>
    if forallb is_ind_type args then [(inductive_mind head, args)] else []
  | _ => []
  end.

(** Collect every [tApp (tInd head_kn _) args] in a term where ALL arguments
    are pure inductive type terms (possibly nested applications).
    Returns [(head_kn, args)] pairs (with duplicates).
    These are the parametric-type applications that can be monomorphised. *)
Fixpoint collect_ind_apps (t : term) : list (kername * list term) :=
  let self_list ts := flat_map collect_ind_apps ts in
  match t with
  | tApp (tInd head _) args =>
    let all_ind := forallb is_ind_type args in
    let here := if all_ind then [(inductive_mind head, args)] else [] in
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

(** Like [collect_eq_arg_kns] but returns [(head_kn, args)] pairs for
    parametric-type applications inside each equality TYPE argument.
    Needed so that e.g. [@eq (list nat) ...] triggers monomorphisation of
    [list nat] → [listnat] via the Step 4b pipeline. *)
Fixpoint collect_eq_arg_ind_apps (t : term) : list (kername * list term) :=
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

(** Deduplicate [(kername * list term)] pairs by canonical-name equality.
    Preserves first-occurrence order. *)
Definition dedup_ind_apps (l : list (kername * list term))
    : list (kername * list term) :=
  fold_left (fun acc p =>
    let match_entry q :=
      andb (eq_kername (fst q) (fst p))
           (andb (Nat.eqb #|snd q| #|snd p|)
                 (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
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

(** Look up [tApp (tInd head_kn _) args] in a mapping whose values are [kername]
    (used for [spec_unlifted_kn_map]).  Args may be nested parametric applications. *)
Definition lookup_app_kn
    (app_kn_mapping : list (kername * list term * kername))
    (f : term) (args : list term) : option kername :=
  match f with
  | tInd head _ =>
    let head_kn := inductive_mind head in
    if forallb is_ind_type args then
      match find (fun e =>
        andb (eq_kername (fst (fst e)) head_kn)
             (andb (Nat.eqb #|snd (fst e)| #|args|)
                   (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                            (combine (snd (fst e)) args))))
        app_kn_mapping with
      | Some e => Some (snd e)
      | None   => None
      end
    else None
  | _ => None
  end.

(** Look up [tApp (tInd head_kn _) args] in a mapping whose values are [inductive]
    (used for [app_kn_mapping] after mutual-block lifting).  Args may be nested
    parametric applications.  Returns [Some lifted_ind] with the correct body index. *)
Definition lookup_app_kn_ind
    (app_kn_mapping : list (kername * list term * inductive))
    (f : term) (args : list term) : option inductive :=
  match f with
  | tInd head _ =>
    let head_kn := inductive_mind head in
    if forallb is_ind_type args then
      match find (fun e =>
        andb (eq_kername (fst (fst e)) head_kn)
             (andb (Nat.eqb #|snd (fst e)| #|args|)
                   (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                            (combine (snd (fst e)) args))))
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
    (app_kn_mapping       : list (kername * list term * inductive))
    (spec_unlifted_kn_map : list ((kername * list term) * kername))
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
    (app_kn_mapping         : list (kername * list term * inductive))
    (spec_unlifted_kn_map   : list ((kername * list term) * kername))
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

(** Recursively replace [tApp (tInd head) args] patterns in a term using
    [app_kn_mapping].  Used to substitute lifted parametric types (e.g.
    [list nat] → [listnat']) inside constructor arg/return types when lifting
    a specialised monomorphic inductive like [prodlistnatlistnat]. *)
Fixpoint subst_app_kns_t
    (app_kn_mapping : list (kername * list term * inductive))
    (t : term) : term :=
  let self := subst_app_kns_t app_kn_mapping in
  match t with
  | tApp (tInd head_ind _) arg_ts =>
    let head_kn := inductive_mind head_ind in
    if forallb is_ind_type arg_ts then
      match find (fun e =>
        andb (eq_kername (fst (fst e)) head_kn)
             (andb (Nat.eqb #|snd (fst e)| #|arg_ts|)
                   (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                            (combine (snd (fst e)) arg_ts))))
        app_kn_mapping with
      | Some (_, new_i) => tInd new_i []
      | None => tApp (tInd head_ind []) (List.map self arg_ts)
      end
    else tApp (tInd head_ind []) (List.map self arg_ts)
  | tProd na ty body   => tProd na (self ty) (self body)
  | tLambda na ty body => tLambda na (self ty) (self body)
  | tLetIn na v ty b   => tLetIn na (self v) (self ty) (self b)
  | tApp f args        => tApp (self f) (List.map self args)
  | _                  => t
  end.

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
    (app_kn_mapping       : list (kername * list term * inductive))
    (spec_unlifted_kn_map : list ((kername * list term) * kername))
    (modes_with_idx       : list ((string * (list nat * list nat)) * list context_decl))
    (fn_app_infos         : list (kername * list term * term))
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
  let anon_b := {| binder_name := nAnon; binder_relevance := Relevant |} in
  (* Resolve an original type term to its lifted version using [full]/[app_kn_mapping]. *)
  let resolve_lifted_tp (tp : term) : term :=
    match tp with
    | tInd ind _ =>
      match find (fun e => eq_kername (fst e) (inductive_mind ind)) full with
      | Some (_, new_i) => tInd new_i []
      | None            => tp
      end
    | tApp (tInd head_ind _) arg_ts =>
      let head_kn := inductive_mind head_ind in
      if negb (forallb is_ind_type arg_ts) then tp
      else
        match find (fun e =>
          andb (eq_kername (fst (fst e)) head_kn)
               (andb (Nat.eqb #|snd (fst e)| #|arg_ts|)
                     (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                              (combine (snd (fst e)) arg_ts))))
          app_kn_mapping with
        | Some (_, new_i) => tInd new_i []
        | None            => tp
        end
    | _ => tp
    end in
  (* Check whether a type term is in the lifting set. *)
  let is_lifted (tp : term) : bool :=
    match tp with
    | tInd ind _ =>
      existsb (fun e => eq_kername (fst e) (inductive_mind ind)) full
    | tApp (tInd head_ind _) arg_ts =>
      let head_kn := inductive_mind head_ind in
      if negb (forallb is_ind_type arg_ts) then false
      else
        existsb (fun e =>
          andb (eq_kername (fst (fst e)) head_kn)
               (andb (Nat.eqb #|snd (fst e)| #|arg_ts|)
                     (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                              (combine (snd (fst e)) arg_ts))))
          app_kn_mapping
    | _ => false
    end in
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
         (* LiftedCstr constructors: one per premise function whose output type
            is this body and that has at least one lifted input argument.
            Each has the same argument signature as the lifted function. *)
         let lifted_ctors :=
           flat_map (fun fi =>
             let fn_kn   := fst (fst fi) in
             let arg_tps := snd (fst fi) in
             let ret_tp  := snd fi in
             match ret_tp with
             | tInd ret_ind _ =>
               if andb (andb (eq_kername (inductive_mind ret_ind) old_kn)
                             (Nat.eqb (inductive_ind ret_ind) i))
                       (existsb is_lifted arg_tps)
               then
                 let n_fn_args := #|arg_tps| in
                 let rel_idx   :=
                   n_par + n_fn_args + block_n_bodies - 1 - block_body_idx in
                 let return_t  :=
                   if Nat.eqb n_par 0 then tRel rel_idx
                   else tApp (tRel rel_idx)
                             (List.map tRel (rev (seq n_fn_args n_par))) in
                 (* cstr_args in snoc order (innermost first) *)
                 let cstr_args :=
                   List.rev (List.map (fun tp =>
                     {| decl_name := anon_b;
                        decl_body := None;
                        decl_type := resolve_lifted_tp tp |})
                     arg_tps) in
                 [{| cstr_name    := snd fn_kn ++ "LiftedCstr";
                     cstr_args    := cstr_args;
                     cstr_indices := [];
                     cstr_type    :=
                       it_mkProd_or_LetIn (List.app params' cstr_args) return_t;
                     cstr_arity   := n_fn_args |}]
               else []
             | _ => []
             end)
           fn_app_infos in
         {| ind_name      := oib.(ind_name) ++ "'";
            ind_indices   := List.map (subst_ind_kns_decl full) oib.(ind_indices);
            ind_sort      := oib.(ind_sort);
            ind_type      := subst_ind_kns full oib.(ind_type);
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              (* Original constructors: step1 (subst knames) + step1b (subst
                 parametric app_kn_mapping, e.g. list nat → listnat') +
                 step2 (lift tRels) + step3 (cross-body tInd → tRel). *)
              List.map (fun c =>
                let args1 := List.map (subst_ind_kns_decl full) c.(cstr_args) in
                let args1' := List.map (fun d =>
                  {| decl_name := d.(decl_name);
                     decl_body := d.(decl_body);
                     decl_type := subst_app_kns_t app_kn_mapping d.(decl_type) |}) args1 in
                let args2 := List.map (lift_decl delta n_par) args1' in
                {| cstr_name    := c.(cstr_name) ++ "'";
                   cstr_args    := s3args args2;
                   cstr_indices := List.map (s3t 0)
                                     (List.map (lift_term delta n_par)
                                       (List.map (subst_ind_kns full) c.(cstr_indices)));
                   cstr_type    := s3t 0
                                     (lift_term delta n_par
                                       (subst_app_kns_t app_kn_mapping
                                         (subst_ind_kns full c.(cstr_type))));
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
              extra
              (* LiftedCstr constructors for premise functions — apply step3. *)
              ++ List.map (fun c =>
                {| cstr_name    := c.(cstr_name);
                   cstr_args    := s3args c.(cstr_args);
                   cstr_indices := List.map (s3t 0) c.(cstr_indices);
                   cstr_type    := s3t 0 c.(cstr_type);
                   cstr_arity   := c.(cstr_arity) |})
              lifted_ctors;
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

(** Collect function-application dependency edges [(output_kn, input_kn)] from
    constructor type [t] traversed under de Bruijn context [ctx] (innermost
    first, index 0 = most recently bound variable).

    For each equality premise [@eq T lhs (tApp fn_head fn_args)] found anywhere
    in [t]:
    - output knames come from the type argument [T]
    - input knames come from the declared types of any [tRel i] among [fn_args]
      (looked up in [ctx])
    Parametric-type applications in [T] or argument types are resolved through
    [spec_kn_pairs] to their monomorphised specialisations when possible. *)
Fixpoint collect_fn_dep_edges_from_ctx
    (spec_kn_pairs : list ((kername * list term) * kername))
    (ctx  : list term)
    (t    : term)
    : list (kername * kername) :=
  let resolve_kns tp :=
    let plain := collect_tind_kns tp in
    let spec_hits :=
      flat_map (fun app =>
        let hkn    := fst app in
        let aterms := snd app in
        match find (fun e =>
          andb (eq_kername (fst (fst e)) hkn)
               (andb (Nat.eqb #|snd (fst e)| #|aterms|)
                     (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                              (combine (snd (fst e)) aterms))))
          spec_kn_pairs with
        | Some e => [snd e]
        | None   => []
        end)
      (collect_ind_apps tp) in
    dedup_kns (List.app plain spec_hits) in
  match t with
  | tProd _ ty body =>
    List.app
      (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx ty)
      (collect_fn_dep_edges_from_ctx spec_kn_pairs (ty :: ctx) body)
  | tLambda _ ty body =>
    List.app
      (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx ty)
      (collect_fn_dep_edges_from_ctx spec_kn_pairs (ty :: ctx) body)
  | tLetIn _ val ty body =>
    List.app
      (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx val)
      (List.app
         (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx ty)
         (collect_fn_dep_edges_from_ctx spec_kn_pairs (ty :: ctx) body))
  | tApp f args =>
    let rec_hits :=
      List.app
        (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx f)
        (flat_map (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx) args) in
    match f with
    | tInd {| inductive_mind := eq_kn |} _ =>
      if String.eqb (snd eq_kn) "eq" then
        match args with
        | T :: _ :: rhs :: _ =>
          let out_kns := resolve_kns T in
          let arg_types :=
            flat_map (fun a =>
              match a with
              | tRel i =>
                match nth_error ctx i with
                | Some tp => [tp]
                | None    => []
                end
              | _ => []
              end)
            (match rhs with
             | tApp (tConstruct _ _ _) _ => []
             | tApp (tInd _ _) _         => []
             | tApp _ fn_args            => fn_args
             | _                         => []
             end) in
          let in_kns := dedup_kns (flat_map resolve_kns arg_types) in
          let edges :=
            flat_map (fun ok =>
              flat_map (fun ik =>
                if eq_kername ok ik then [] else [(ok, ik)])
              in_kns)
            out_kns in
          List.app edges rec_hits
        | _ => rec_hits
        end
      else rec_hits
    | _ => rec_hits
    end
  | tCase _ pred disc brs =>
    List.app
      (flat_map (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx) pred.(pparams))
      (List.app
         (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx pred.(preturn))
         (List.app
            (collect_fn_dep_edges_from_ctx spec_kn_pairs ctx disc)
            (flat_map (fun br =>
               collect_fn_dep_edges_from_ctx spec_kn_pairs ctx br.(bbody)) brs)))
  | _ => []
  end.

(** Collect [(fn_kn, [arg_type_terms], ret_type_term)] for each named function
    applied in an equality premise inside constructor type [t], using de Bruijn
    context [ctx] (innermost first).

    For each premise [@eq T lhs (tApp (tConst fn_kn _) fn_args)]:
    - [ret_type] = T
    - [arg_types] = types of each [tRel i] argument, looked up in [ctx]
    Only emits an entry when ALL arguments are [tRel] nodes (so that every
    arg type is resolvable from the context). *)
Fixpoint collect_fn_app_info_from_ctx
    (ctx : list term)
    (t   : term)
    : list (kername * list term * term) :=
  match t with
  | tProd _ ty body =>
    List.app
      (collect_fn_app_info_from_ctx ctx ty)
      (collect_fn_app_info_from_ctx (ty :: ctx) body)
  | tLambda _ ty body =>
    List.app
      (collect_fn_app_info_from_ctx ctx ty)
      (collect_fn_app_info_from_ctx (ty :: ctx) body)
  | tLetIn _ val ty body =>
    List.app (collect_fn_app_info_from_ctx ctx val)
    (List.app (collect_fn_app_info_from_ctx ctx ty)
              (collect_fn_app_info_from_ctx (ty :: ctx) body))
  | tApp f args =>
    let rec_hits :=
      List.app
        (collect_fn_app_info_from_ctx ctx f)
        (flat_map (collect_fn_app_info_from_ctx ctx) args) in
    match f with
    | tInd {| inductive_mind := eq_kn |} _ =>
      if String.eqb (snd eq_kn) "eq" then
        match args with
        | ret_tp :: _ :: rhs :: _ =>
          match rhs with
          | tApp (tConst fn_kn _) fn_args =>
            let maybe_types :=
              List.map (fun a =>
                match a with
                | tRel i => nth_error ctx i
                | _      => None
                end) fn_args in
            if forallb (fun o => match o with Some _ => true | None => false end) maybe_types
            then
              let arg_types :=
                flat_map (fun o => match o with Some tp => [tp] | None => [] end) maybe_types in
              List.app [(fn_kn, arg_types, ret_tp)] rec_hits
            else rec_hits
          | _ => rec_hits
          end
        | _ => rec_hits
        end
      else rec_hits
    | _ => rec_hits
    end
  | tCase _ pred disc brs =>
    List.app
      (flat_map (collect_fn_app_info_from_ctx ctx) pred.(pparams))
      (List.app (collect_fn_app_info_from_ctx ctx pred.(preturn))
      (List.app (collect_fn_app_info_from_ctx ctx disc)
                (flat_map (fun br =>
                   collect_fn_app_info_from_ctx ctx br.(bbody)) brs)))
  | _ => []
  end.

(** Skip [n] leading [tProd] binders and return the remainder of the type.
    Used to extract return types from constant types: [skip_prods (arity fn) cst_type]. *)
Fixpoint skip_prods (n : nat) (t : term) : term :=
  match n with
  | 0   => t
  | S k => match t with
            | tProd _ _ body => skip_prods k body
            | _              => t
            end
  end.

(** Extract the first [n] argument types from a [tProd]-chain,
    skipping [skip] leading binders (parameters).
    Forward-declared here so it is available to the constructor-scanning helpers below. *)
Fixpoint extract_arg_types_early (skip n : nat) (t : term) : list term :=
  match skip with
  | S k => match t with
            | tProd _ _ body => extract_arg_types_early k n body
            | _ => []
            end
  | 0 =>
    match n, t with
    | 0, _            => []
    | _, tSort _      => []
    | S k, tProd _ ty body => ty :: extract_arg_types_early 0 k body
    | _, _ => []
    end
  end.

(** Extract the first [n] arg types and the return type from a [tProd]-chain in one pass. *)
Definition fn_info_from_cst_type (n : nat) (cst_ty : term) : list term * term :=
  (extract_arg_types_early 0 n cst_ty, skip_prods n cst_ty).

(** Given a list of (arg_term, ret_type) pairs from a relation application or
    conclusion index, emit [(fn_kn, arg_types, ret_tp)] for each pair where
    arg_term = [tApp (tConst fn_kn) fn_args] and all fn_args are [tRel] nodes
    resolvable in [ctx] (innermost at index 0). *)
Definition collect_fn_apps_from_arg_pairs
    (ctx   : list term)
    (pairs : list (term * term))
    : list (kername * list term * term) :=
  flat_map (fun pair =>
    let arg_tm := fst pair in
    let ret_tp := snd pair in
    match arg_tm with
    | tApp (tConst fn_kn _) fn_args =>
      let maybe_types := List.map (fun a =>
        match a with
        | tRel i => nth_error ctx i
        | _ => None
        end) fn_args in
      if forallb (fun o => match o with Some _ => true | None => false end) maybe_types
      then
        let arg_types :=
          flat_map (fun o => match o with Some tp => [tp] | None => [] end) maybe_types in
        [(fn_kn, arg_types, ret_tp)]
      else []
    | _ => []
    end)
  pairs.

(** Scan [cstr_indices] for direct function applications [tApp (tConst fn_kn) fn_args]
    where all fn_args are [tRel] nodes resolvable in [full_ctx] (the types of [cstr_args],
    innermost at index 0).  [idx_types] are the declared index types of the relation
    extracted from [oib.ind_type]; they provide the [ret_type] for each index position. *)
Definition collect_fn_app_info_from_indices
    (full_ctx  : list term)
    (idx_types : list term)
    (cstr_idx  : list term)
    : list (kername * list term * term) :=
  collect_fn_apps_from_arg_pairs full_ctx (combine cstr_idx idx_types).

(** Recursively scan a premise term [t] under de Bruijn context [ctx] for
    relation applications [tApp (tInd rel_ind) rel_args] where [rel_ind] is
    tracked in [rel_minds_assoc].  For each such application, any argument
    position that is [tApp (tConst fn_kn) fn_args] (all args being [tRel]
    nodes) emits [(fn_kn, arg_types, ret_type)] using the relation's declared
    index types to supply [ret_type].  Also recurses into sub-terms so that
    nested applications (e.g. inside conjunctions) are found. *)
Fixpoint collect_fn_app_info_from_prem
    (rel_minds_assoc : list (kername * mutual_inductive_body))
    (ctx : list term)
    (t   : term)
    : list (kername * list term * term) :=
  match t with
  | tProd _ ty body =>
    List.app
      (collect_fn_app_info_from_prem rel_minds_assoc ctx ty)
      (collect_fn_app_info_from_prem rel_minds_assoc (ty :: ctx) body)
  | tLambda _ ty body =>
    List.app
      (collect_fn_app_info_from_prem rel_minds_assoc ctx ty)
      (collect_fn_app_info_from_prem rel_minds_assoc (ty :: ctx) body)
  | tLetIn _ val ty body =>
    List.app
      (collect_fn_app_info_from_prem rel_minds_assoc ctx val)
    (List.app
      (collect_fn_app_info_from_prem rel_minds_assoc ctx ty)
      (collect_fn_app_info_from_prem rel_minds_assoc (ty :: ctx) body))
  | tApp f args =>
    let rec_hits :=
      List.app
        (collect_fn_app_info_from_prem rel_minds_assoc ctx f)
        (flat_map (collect_fn_app_info_from_prem rel_minds_assoc ctx) args) in
    match f with
    | tInd rel_ind _ =>
      let kn   := inductive_mind rel_ind in
      let bidx := inductive_ind  rel_ind in
      if String.eqb (snd kn) "eq" then rec_hits  (* @eq handled by collect_fn_app_info_from_ctx *)
      else
        match find (fun p => eq_kername (fst p) kn) rel_minds_assoc with
        | None => rec_hits
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => rec_hits
          | Some oib =>
            let idx_types := extract_arg_types_early mind.(ind_npars) 100 oib.(ind_type) in
            List.app
              (collect_fn_apps_from_arg_pairs ctx (combine args idx_types))
              rec_hits
          end
        end
    | _ => rec_hits
    end
  | _ => []
  end.

(** Scan a constructor's premises ([cstr_args]), conclusion ([cstr_type]),
    and index terms ([cstr_indices]) and return all [(fn_kn, arg_types, ret_type)]
    entries.

    - Premises are scanned for equality sub-terms [@eq T lhs (f args)] and for
      relation applications [tApp (tInd rel_ind) rel_args] where a rel_arg is
      a function application (new: requires [rel_minds_assoc]).
    - [cstr_type] is scanned for further equality sub-terms.
    - [cstr_indices] are scanned for direct [tApp (tConst fn_kn) fn_args]
      applications using [idx_types] for [ret_type]. *)
Definition collect_fn_app_info_from_ctor
    (idx_types       : list term)
    (rel_minds_assoc : list (kername * mutual_inductive_body))
    (c : constructor_body)
    : list (kername * list term * term) :=
  let (_, prem_infos) :=
    fold_left (fun p d =>
      let ctx := fst p in
      let acc := snd p in
      let eq_hits  := collect_fn_app_info_from_ctx  ctx d.(decl_type) in
      let rel_hits := collect_fn_app_info_from_prem rel_minds_assoc ctx d.(decl_type) in
      (d.(decl_type) :: ctx, List.app acc (List.app eq_hits rel_hits)))
    (List.rev c.(cstr_args))
    ([], []) in
  let full_ctx  := List.map decl_type c.(cstr_args) in
  let idx_infos := collect_fn_app_info_from_indices full_ctx idx_types c.(cstr_indices) in
  List.app prem_infos (List.app (collect_fn_app_info_from_ctx [] c.(cstr_type)) idx_infos).

(** Scan a term for ALL [tApp (tConst fn_kn) fn_args] sub-terms where every
    argument is a [tRel] resolvable in [ctx].  Returns [(fn_kn, arg_types)]
    without a [ret_type]; callers look that up via [tmQuoteConstant].
    This catches function applications nested inside constructor applications
    that the equality-pattern scanner misses. *)
Fixpoint collect_const_fn_kns_from_ctx
    (ctx : list term)
    (t   : term)
    : list (kername * list term) :=
  match t with
  | tProd _ ty body =>
    List.app
      (collect_const_fn_kns_from_ctx ctx ty)
      (collect_const_fn_kns_from_ctx (ty :: ctx) body)
  | tLambda _ ty body =>
    List.app
      (collect_const_fn_kns_from_ctx ctx ty)
      (collect_const_fn_kns_from_ctx (ty :: ctx) body)
  | tLetIn _ val ty body =>
    List.app (collect_const_fn_kns_from_ctx ctx val)
    (List.app (collect_const_fn_kns_from_ctx ctx ty)
              (collect_const_fn_kns_from_ctx (ty :: ctx) body))
  | tApp f args =>
    let rec_hits :=
      List.app
        (collect_const_fn_kns_from_ctx ctx f)
        (flat_map (collect_const_fn_kns_from_ctx ctx) args) in
    match f with
    | tConst fn_kn _ =>
      let maybe_types := List.map (fun a =>
        match a with
        | tRel i => nth_error ctx i
        | _      => None
        end) args in
      if forallb (fun o => match o with Some _ => true | None => false end) maybe_types
      then
        let arg_types :=
          flat_map (fun o => match o with Some tp => [tp] | None => [] end) maybe_types in
        List.app [(fn_kn, arg_types)] rec_hits
      else
        (* Some args are nested calls (not tRel). Still record fn_kn with a
           dummy list of the right length so the arity is preserved for
           extra_fn_infos_r, which will recover the true types from the
           constant's declaration via extract_arg_types_early. *)
        List.app [(fn_kn, List.repeat (tSort sProp) (List.length args))] rec_hits
    | _ => rec_hits
    end
  | _ => []
  end.

(** Collect all [(fn_kn, arg_types)] pairs from a constructor by scanning
    [cstr_args], [cstr_type], and [cstr_indices] with [collect_const_fn_kns_from_ctx].
    This finds function applications nested inside constructor applications in
    index terms (e.g. [Nat.add] inside [Seq (m+n) s2]), which the
    equality-pattern and top-level-index scanners miss. *)
Definition collect_const_fn_kns_from_ctor (c : constructor_body)
    : list (kername * list term) :=
  let prem_pairs :=
    snd (fold_left (fun p d =>
           let ctx := fst p in
           let acc := snd p in
           (d.(decl_type) :: ctx,
            List.app acc (collect_const_fn_kns_from_ctx ctx d.(decl_type))))
         (List.rev c.(cstr_args))
         ([], [])) in
  let full_ctx := List.map decl_type c.(cstr_args) in
  let idx_pairs  := flat_map (collect_const_fn_kns_from_ctx full_ctx) c.(cstr_indices) in
  let type_pairs := collect_const_fn_kns_from_ctx [] c.(cstr_type) in
  List.app prem_pairs (List.app type_pairs idx_pairs).

(** Same as [collect_fn_app_info_from_ctor] but returns dependency edges
    [(out_kn, in_kn)] for [collect_fn_dep_edges_from_ctx].
    Also scans [cstr_indices] and relation-application premises. *)
Definition collect_fn_dep_edges_from_ctor
    (spec_kn_pairs   : list ((kername * list term) * kername))
    (idx_types       : list term)
    (rel_minds_assoc : list (kername * mutual_inductive_body))
    (c : constructor_body)
    : list (kername * kername) :=
  let resolve_kns (tp : term) :=
    let plain := collect_tind_kns tp in
    let spec_hits :=
      flat_map (fun app =>
        let hkn    := fst app in
        let aterms := snd app in
        match find (fun e =>
          andb (eq_kername (fst (fst e)) hkn)
               (andb (Nat.eqb #|snd (fst e)| #|aterms|)
                     (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                              (combine (snd (fst e)) aterms))))
          spec_kn_pairs with
        | Some e => [snd e]
        | None   => []
        end)
      (collect_ind_apps tp) in
    dedup_kns (List.app plain spec_hits) in
  let edges_from_pairs (ctx : list term) (pairs : list (term * term)) :=
    flat_map (fun pair =>
      let arg_tm := fst pair in
      let ret_tp := snd pair in
      match arg_tm with
      | tApp (tConst _ _) fn_args =>
        let arg_types :=
          flat_map (fun a =>
            match a with
            | tRel i => match nth_error ctx i with Some tp => [tp] | None => [] end
            | _ => []
            end) fn_args in
        let out_kns := resolve_kns ret_tp in
        let in_kns  := dedup_kns (flat_map resolve_kns arg_types) in
        flat_map (fun ok => flat_map (fun ik =>
          if eq_kername ok ik then [] else [(ok, ik)]) in_kns) out_kns
      | _ => []
      end) pairs in
  let (_, prem_edges) :=
    fold_left (fun p d =>
      let ctx := fst p in
      let acc := snd p in
      let eq_edges  := collect_fn_dep_edges_from_ctx spec_kn_pairs ctx d.(decl_type) in
      let rel_fn_infos :=
        collect_fn_app_info_from_prem rel_minds_assoc ctx d.(decl_type) in
      let rel_edges :=
        flat_map (fun fi =>
          let ret_tp    := snd fi in
          let arg_types := snd (fst fi) in
          let out_kns   := resolve_kns ret_tp in
          let in_kns    := dedup_kns (flat_map resolve_kns arg_types) in
          flat_map (fun ok => flat_map (fun ik =>
            if eq_kername ok ik then [] else [(ok, ik)]) in_kns) out_kns)
        rel_fn_infos in
      (d.(decl_type) :: ctx, List.app acc (List.app eq_edges rel_edges)))
    (List.rev c.(cstr_args))
    ([], []) in
  let full_ctx := List.map decl_type c.(cstr_args) in
  let idx_edges := edges_from_pairs full_ctx (combine c.(cstr_indices) idx_types) in
  List.app prem_edges
    (List.app (collect_fn_dep_edges_from_ctx spec_kn_pairs [] c.(cstr_type)) idx_edges).

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
    (worklist      : list kername)
    (lifting       : list kername)
    (explored      : list kername)
    (rel_kns       : list kername)
    (fn_dep_edges  : list (kername * kername))
    (fuel          : nat)
    : TemplateMonad (list kername) :=
  match fuel with
  | 0 =>
    tmFail ("expand_dep_closure: BFS ran out of fuel with " ++
            string_of_nat (List.length worklist) ++
            " types still in the worklist: " ++
            String.concat ", " (List.map snd worklist))
  | S f =>
    match worklist with
    | [] => tmReturn lifting
    | kn :: rest =>
      if orb (existsb (eq_kername kn) explored)
             (existsb (eq_kername kn) rel_kns)
      then expand_dep_closure rest lifting explored rel_kns fn_dep_edges f
      else
        mind <- tmQuoteInductive kn ;;
        if orb (is_prop_mind mind) (negb (Nat.eqb mind.(ind_npars) 0))
        then expand_dep_closure rest lifting
               (dedup_kns (explored ++ [kn])) rel_kns fn_dep_edges f
        else
          let ctor_arg_kns :=
            dedup_kns (flat_map (fun oib =>
              flat_map (fun c => collect_tind_kns c.(cstr_type))
                       oib.(ind_ctors))
            mind.(ind_bodies)) in
          (* Function-application dep edges: types that [kn] depends on as the
             output type of some premise function (e.g. if [f : T → kn] was
             found in an equality premise, [T] is a fn_dep of [kn]). *)
          let fn_dep_kns :=
            dedup_kns (flat_map
              (fun e => if eq_kername (fst e) kn then [snd e] else [])
              fn_dep_edges) in
          let all_dep_kns := dedup_kns (ctor_arg_kns ++ fn_dep_kns) in
          let new_in_wl :=
            filter (fun kn' =>
              andb (negb (existsb (eq_kername kn') explored))
                   (negb (existsb (eq_kername kn') rest)))
              all_dep_kns in
          let new_lifting :=
            if andb (negb (existsb (eq_kername kn) lifting))
                    (existsb (fun kn' =>
                       existsb (eq_kername kn') lifting) all_dep_kns)
            then dedup_kns (lifting ++ [kn])
            else lifting in
          expand_dep_closure
            (rest ++ new_in_wl)
            new_lifting
            (dedup_kns (explored ++ [kn]))
            rel_kns fn_dep_edges f
    end
  end.

(** Fixpoint wrapper around [expand_dep_closure]: re-runs BFS with a fresh
    [explored] set each iteration, using the previous iteration's [lifting] as
    the new seed, until the lifting set stabilises (no new types added).
    [outer_fuel] bounds the number of iterations; fails with [tmFail] if
    lifting has not stabilised by then.  Each inner BFS is given [inner_fuel]
    steps; if it exhausts that, the inner [tmFail] propagates immediately. *)
Polymorphic Fixpoint expand_dep_closure_fix
    (initial_worklist : list kername)
    (lifting          : list kername)
    (rel_kns          : list kername)
    (fn_dep_edges     : list (kername * kername))
    (inner_fuel       : nat)
    (outer_fuel       : nat)
    : TemplateMonad (list kername) :=
  match outer_fuel with
  | 0 =>
    tmFail ("expand_dep_closure_fix: lifting set did not stabilise after " ++
            string_of_nat inner_fuel ++
            " BFS passes; current lifting set: " ++
            String.concat ", " (List.map snd lifting))
  | S f =>
    lifting' <- expand_dep_closure initial_worklist lifting [] rel_kns fn_dep_edges inner_fuel ;;
    if Nat.eqb (List.length lifting') (List.length lifting)
    then tmReturn lifting'
    else expand_dep_closure_fix initial_worklist lifting' rel_kns fn_dep_edges inner_fuel f
  end.

(** Given a [mode_map], find all non-Prop types occurring as argument types
    of the listed relations, declare lifted copies, and return:
    - [type_mapping]   : old kname → new kname for each lifted data type
    - [app_kn_mapping] : (head_kn, [arg_kns], lifted_spec_kn) for each
      parametric application (e.g. [list nat]) that was monomorphised to a
      fresh inductive (e.g. [listnat']) before lifting.

    Parametric-type applications found in index types are specialised first
    (Step 4b) and then lifted by the same pipeline as monomorphic types. *)

(** Extract the first [n] argument types from a [tProd]-chain,
    skipping [skip] leading binders (parameters).
    Used here and in later generation passes. *)
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

Unset Universe Checking.
Polymorphic Definition preprocess_coind_types
    (modes       : mode_map)
    (fuel        : nat)
    : TemplateMonad (list (kername * inductive) * list (kername * list term * inductive)) :=
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
        | Some d =>
          (* Only collect the direct head kname of each mode-position type;
             do NOT recurse into type arguments.  Constituent types like [nat]
             from [list nat] must NOT enter the lifting set automatically — they
             only belong there if a function applied in a constructor returns them. *)
          match d.(decl_type) with
          | tInd ind _  => [inductive_mind ind]
          | tApp f' _   => match f' with tInd ind _ => [inductive_mind ind] | _ => [] end
          | _           => []
          end
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
          flat_map (fun d => collect_ind_apps_toplevel d.(decl_type)) (snd mwi))
        modes_with_idx)
       ++ ctor_eq_ind_apps_raw) in
  spec_kn_pairs <- monad_fold_left (fun acc entry =>
    let head_kn    := fst entry in
    let arg_terms_e := snd entry in
    head_mind <- tmQuoteInductive head_kn ;;
    if Nat.eqb head_mind.(ind_npars) 0 then tmReturn acc  (* already monomorphic *)
    else
      let spec_name :=
        fold_left (fun s t => s ++ ind_type_name t) arg_terms_e (snd head_kn) in
      (* MetaRocq de Bruijn: after strip_leading_prods n, the last param sits at
         tRel 0 and the first at tRel (n-1).  subst s 0 maps tRel i → s[i], so
         s must be in reverse parameter order to match. *)
      let concrete_args := List.rev arg_terms_e in
      spec_body <- tmEval all (specialize_mind head_mind head_kn concrete_args spec_name) ;;
      tmMkInductivePreserveFinite spec_body ;;
      refs <- tmLocate spec_name ;;
      let spec_kn :=
        match find (fun g =>
          match g with IndRef _ => true | _ => false end) refs with
        | Some (IndRef ind) => inductive_mind ind
        | _                 => (cur_mp, spec_name)
        end in
      tmReturn (List.app acc [(entry, spec_kn)]))
    raw_ind_apps [] ;;
  spec_kn_pairs <- tmEval all spec_kn_pairs ;;
  let spec_kns := List.map snd spec_kn_pairs in
  (* Step 4c: compute function-application dependency edges (pure).
     For each relation constructor type, traverse with a de Bruijn context to
     find equality premises [@eq T lhs (f arg1 … argN)].  The output type [T]
     and the declared types of any [tRel] arguments (from the context) give
     edges [(out_kn, in_kn)], resolved through [spec_kn_pairs] for parametric
     types.  These edges are passed to [expand_dep_closure] so that if out_kn
     is in the lifting set, in_kn is also explored and potentially lifted. *)
  let fn_dep_edges :=
    flat_map (fun km =>
      let n_params := (snd km).(ind_npars) in
      flat_map (fun oib =>
        let idx_types := extract_arg_types n_params 100 oib.(ind_type) in
        flat_map (fun c =>
          collect_fn_dep_edges_from_ctor spec_kn_pairs idx_types rel_block_minds c)
                 oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds in
  (* Collect function application info (equality premises, relation-application
     premises, and direct indices in the conclusion). *)
  let fn_app_infos_base :=
    fold_left (fun acc fi =>
      if existsb (fun e => eq_kername (fst (fst e)) (fst (fst fi))) acc
      then acc else List.app acc [fi])
    (flat_map (fun km =>
      let n_params := (snd km).(ind_npars) in
      flat_map (fun oib =>
        let idx_types := extract_arg_types n_params 100 oib.(ind_type) in
        flat_map (fun c =>
          collect_fn_app_info_from_ctor idx_types rel_block_minds c)
                 oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds)
    [] in
  (* Also scan for function applications nested inside constructor applications
     in index terms (e.g. [Nat.add m n] inside [Seq (m+n) s2]).  For each
     new fn_kn not already in fn_app_infos_base, look up the return type from
     the global environment. *)
  let extra_fn_pairs :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds in
  let new_fn_pairs :=
    fold_left (fun acc p =>
      let fn_kn := fst p in
      if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) fn_app_infos_base)
             (existsb (fun q => eq_kername (fst q) fn_kn) acc)
      then acc
      else List.app acc [p])
    extra_fn_pairs [] in
  extra_fn_infos <- monad_map (fun p =>
    let fn_kn := fst p in
    let n     := List.length (snd p) in
    cb <- tmQuoteConstant fn_kn false ;;
    let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
    tmReturn (fn_kn, decl_arg_types, ret_tp)) new_fn_pairs ;;
  let fn_app_infos := List.app fn_app_infos_base extra_fn_infos in
  fn_app_infos <- tmEval all fn_app_infos ;;
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
     constructor argument type (or function-application dep) already in the
     lifting set. *)
  type_kns <- expand_dep_closure_fix (type_kns ++ eq_seed_kns) type_kns rel_kns fn_dep_edges fuel fuel ;;
  type_kns <- tmEval all type_kns ;;
  let pre_mapping := List.map (fun kn => (kn, (cur_mp, snd kn ++ "'"))) type_kns in
  (* Helper: given a term [t], return the lifted knames it mentions —
     either as a plain [tInd kn] in [pre_mapping], or as a recognised
     parametric application [tApp (tInd head) [tInd arg...]] in [spec_kn_pairs]. *)
  let lookup_lifted_kns t :=
    let spec_hits :=
      flat_map (fun entry =>
        let head_kn    := fst (fst entry) in
        let arg_terms_e := snd (fst entry) in
        let spec_kn    := snd entry in
        flat_map (fun app =>
          if andb (eq_kername (fst app) head_kn)
                  (andb (Nat.eqb #|snd app| #|arg_terms_e|)
                        (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                                 (combine (snd app) arg_terms_e)))
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
  type_minds <- tmEval all type_minds ;;
  (* Spec-derived dep edges: if spec_kn [outer] was built by specialising
     head_kn at args that include another spec_kn [inner] (e.g.
     prodlistnatlistnat was built from prod applied to [list nat, list nat]
     and listnat was built from list applied to [nat]), then outer must come
     AFTER inner in the topo sort so that outerLift can call innerLift. *)
  let spec_dep_edges :=
    flat_map (fun outer_entry =>
      let outer_spec_kn := snd outer_entry in
      flat_map (fun arg_t =>
        match arg_t with
        | tApp (tInd head_ind _) inner_args =>
          let head_kn2 := inductive_mind head_ind in
          match find (fun inner_entry =>
            andb (eq_kername (fst (fst inner_entry)) head_kn2)
                 (andb (Nat.eqb #|snd (fst inner_entry)| #|inner_args|)
                       (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                                (combine (snd (fst inner_entry)) inner_args))))
            spec_kn_pairs with
          | Some inner_entry =>
            let inner_spec_kn := snd inner_entry in
            if eq_kername outer_spec_kn inner_spec_kn then []
            else [(outer_spec_kn, inner_spec_kn)]
          | None => []
          end
        | _ => []
        end)
      (snd (fst outer_entry)))
    spec_kn_pairs in
  let sorted_kns :=
    topo_sort_kns type_kns type_minds pre_mapping
      (List.app mode_dep_pairs spec_dep_edges) [] (S #|type_kns|) in
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
      let head_kn    := fst (fst e) in
      let arg_terms_e := snd (fst e) in
      let spec_kn    := snd e in
      match find (fun p => eq_kername (fst p) spec_kn) pre_ind_mapping with
      | Some (_, lifted_ind) => [((head_kn, arg_terms_e), lifted_ind)]
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
          pre_app_kn_mapping spec_kn_pairs modes_with_idx fn_app_infos 1 0 in
      tmReturn (List.app acc [(kn, body)])
    end)
  sorted_kns [] ;;
  computed_bodies <- tmEval all computed_bodies ;;
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
          let head_kn    := fst (fst e) in
          let arg_terms_e := snd (fst e) in
          let spec_kn    := snd e in
          match find (fun p => eq_kername (fst p) spec_kn) group_ind_mapping with
          | Some (_, grp_ind) => [((head_kn, arg_terms_e), grp_ind)]
          | None =>
            match find (fun p => eq_kername (fst p) spec_kn) acc with
            | Some (_, acc_ind) => [((head_kn, arg_terms_e), acc_ind)]
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
                       grp_app_kn_mapping spec_kn_pairs modes_with_idx fn_app_infos
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
      combined_ev <- tmEval all combined ;;
      tmMkInductivePreserveFinite combined_ev ;;
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
  actual_mapping <- tmEval all actual_mapping ;;
  let final_app_kn_mapping :=
    flat_map (fun e =>
      let head_kn    := fst (fst e) in
      let arg_terms_e := snd (fst e) in
      let spec_kn    := snd e in
      match find (fun p => eq_kername (fst p) spec_kn) actual_mapping with
      | Some (_, lifted_ind) => [((head_kn, arg_terms_e), lifted_ind)]
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
    (app_kn_mapping : list (kername * list term * inductive))
    (f : term) (args : list term)
    : option (inductive * nat) :=
  match f with
  | tConstruct ind _ _ =>
    let head_kn := inductive_mind ind in
    match find (fun e =>
      let arg_terms := snd (fst e) in
      let n_params  := #|arg_terms| in
      andb (eq_kername (fst (fst e)) head_kn)
      (if Nat.leb n_params #|args| then
        let type_args := firstn n_params args in
        if forallb is_ind_type type_args then
          andb (Nat.eqb #|type_args| #|arg_terms|)
               (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                        (combine arg_terms type_args))
        else false
      else false)) app_kn_mapping with
    | None   => None
    | Some e => Some (snd e, #|snd (fst e)|)
    end
  | _ => None
  end.

(** Substitute both [tInd] and [tConstruct] knames throughout a term.
    Also resolves parametric-type applications via [app_kn_mapping]:
    [tApp (tInd head_kn _) [tInd arg_kn _; ...]] → [tInd lifted_spec_kn []]
    when a monomorphic specialisation exists.  The [tApp] check runs BEFORE
    recursive descent so original arg knames are used for the lookup. *)
Fixpoint subst_inds_and_ctors
    (app_kn_mapping : list (kername * list term * inductive))
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
    (app_kn_mapping : list (kername * list term * inductive))
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
    (app_kn_mapping : list (kername * list term * inductive))
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
                               (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
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

(** Replace [tConst old_kn] with [tConst new_kn] for each [(old_kn, new_kn)]
    in [fn_kn_map].  Used to rewrite equality-premise function calls to their
    lifted counterparts when building the lifted relation body. *)
Fixpoint subst_const_kns (fn_kn_map : list (kername * kername)) (t : term) : term :=
  let sub := subst_const_kns fn_kn_map in
  match t with
  | tConst kn univs =>
    match find (fun e => eq_kername (fst e) kn) fn_kn_map with
    | Some (_, new_kn) => tConst new_kn univs
    | None             => t
    end
  | tApp f args         => tApp (sub f) (List.map sub args)
  | tProd na ty body    => tProd na (sub ty) (sub body)
  | tLambda na ty body  => tLambda na (sub ty) (sub body)
  | tLetIn na v ty body => tLetIn na (sub v) (sub ty) (sub body)
  | tCase ci pred disc brs =>
    tCase ci
      {| pparams  := List.map sub pred.(pparams);
         puinst   := pred.(puinst);
         pcontext := pred.(pcontext);
         preturn  := sub pred.(preturn) |}
      (sub disc)
      (List.map (fun br =>
        {| bcontext := br.(bcontext); bbody := sub br.(bbody) |}) brs)
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

Definition subst_const_kns_decl (fn_kn_map : list (kername * kername)) (d : context_decl)
    : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map (subst_const_kns fn_kn_map) d.(decl_body);
     decl_type := subst_const_kns fn_kn_map d.(decl_type) |}.

(** Build the lifted [mutual_inductive_body] for a relation block,
    appending a [<rel>'Undefined] constructor to every body. *)
Definition make_lifted_relation_mind
    (old_mind       : mutual_inductive_body)
    (old_rel_kn     : kername)
    (new_rel_kn     : kername)
    (rel_mapping    : list (kername * inductive))
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    (type_body_map  : list (inductive * one_inductive_body))
    (fn_kn_map      : list (kername * kername))
    : mutual_inductive_body :=
  let new_rel_ind  := {| inductive_mind := new_rel_kn; inductive_ind := 0 |} in
  let full_mapping := (old_rel_kn, new_rel_ind) :: rel_mapping ++ type_mapping in
  let sub_ty   t := subst_const_kns fn_kn_map (subst_inds_and_ctors app_kn_mapping full_mapping t) in
  let sub_decl d := subst_const_kns_decl fn_kn_map (subst_inds_and_ctors_decl app_kn_mapping full_mapping d) in
  let params'  := List.map sub_decl old_mind.(ind_params) in
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
            ind_indices   := List.map sub_decl oib.(ind_indices);
            ind_sort      := oib.(ind_sort);
            ind_type      := sub_ty oib.(ind_type);
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              List.map (fun c =>
                {| cstr_name    := c.(cstr_name) ++ "'";
                   cstr_args    := List.map sub_decl c.(cstr_args);
                   cstr_indices := List.map sub_ty c.(cstr_indices);
                   cstr_type    := sub_ty c.(cstr_type);
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
    (app_kn_mapping : list (kername * list term * inductive))
    (modes          : mode_map)
    (fn_kn_map      : list (kername * kername))
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
  lifted_rel_mind <- tmEval all
    (make_lifted_relation_mind old_mind rel_kn new_rel_kn rel_mapping type_mapping
       app_kn_mapping modes_with_idx type_body_map fn_kn_map) ;;
  tmMkInductivePreserveFinite lifted_rel_mind.


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
    (old_kn      : kername)
    (n_args      : nat)
    (snoc_i      : nat)
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (t           : term) : option (option kername) :=
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
  | tApp (tInd head_ind _) arg_ts =>
    (* Parametric application like [list nat]: find the spec'd type via
       app_kn_map, then reverse-lookup in type_map for the old spec_kn name
       (needed to form [spec_knLift]). *)
    let head_kn := inductive_mind head_ind in
    if forallb is_ind_type arg_ts then
      match find (fun e =>
        andb (eq_kername (fst (fst e)) head_kn)
             (andb (Nat.eqb #|snd (fst e)| #|arg_ts|)
                   (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                            (combine (snd (fst e)) arg_ts))))
        app_kn_map with
      | Some (_, lifted_ind) =>
        match find (fun p =>
          andb (eq_kername (inductive_mind (snd p)) (inductive_mind lifted_ind))
               (Nat.eqb (inductive_ind (snd p)) (inductive_ind lifted_ind)))
          type_map with
        | Some (spec_kn, _) =>
          if eq_kername spec_kn old_kn then Some None
          else Some (Some spec_kn)
        | None => None
        end
      | None => None
      end
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
    (old_kn      : kername)
    (oib         : one_inductive_body)
    (new_ind     : inductive)
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (cur_mp      : modpath)
    (orig_form   : option (kername * list term))
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
    | None                 => []
    | Some (_, arg_terms)  => arg_terms
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
          match lift_arg_class old_kn n_args snoc_i type_map app_kn_map arg_t with
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
    (app_kn_map  : list (kername * list term * inductive))
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
              let d := make_lift_def old_kn oib new_ind all_map app_kn_map cur_mp orig_form in
              let fn_term := if is_coind then tCoFix [d] 0 else tFix [d] 0 in
              fn_term_ev <- tmEval all fn_term ;;
              tmMkDefinition (snd old_kn ++ "Lift") fn_term_ev
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
    (app_kn_map : list (kername * list term * inductive))
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
      let par_terms := snd (fst e) in
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
    (app_kn_map : list (kername * list term * inductive))
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
    (app_kn_map : list (kername * list term * inductive))
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
    (app_kn_map  : list (kername * list term * inductive))
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
                   let fnSymb_ty := make_fnSymb_type new_ind n_bodies n_params c type_map app_kn_map in
                   fnSymb_ty_ev <- tmEval all fnSymb_ty ;;
                   tmMkParameter (c.(cstr_name) ++ "fnSymb") fnSymb_ty_ev))
                extra (tmReturn tt)
            end) (fun _ =>
    generate_fnSymb_params rest type_map app_kn_map)))
  end.

(* ================================================================== *)
(** ** Rest function generation                                        *)
(* ================================================================== *)

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
    (todo    : list (inductive * (string * (list nat * list nat))))
    (cur_mp  : modpath)
    (prod_kn : kername)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | (block_ind, (rel_name, (in_pos, out_pos))) :: rest_todo =>
    (* The lifted block is registered under snd(block_kn) ++ prime,
       so we quote that block and then search for the body by name. *)
    let lifted_block_kn := (cur_mp, snd (inductive_mind block_ind) ++ "'") in
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
      fn_term_ev <- tmEval all fn_term ;;
      tmBind (tmMkDefinition (rel_name ++ "'Rest") fn_term_ev) (fun _ =>
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
    (app_kn_map : list (kername * list term * inductive))
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

(** Plain (non-holey) push: maps [new_ind] back to the original type, returning [T]
    directly.  Used by [generate_lifted_fns] so that liftedFunc definitions (e.g.
    [substliftedFunc]) can call the original function with concrete [T] values.
    Identical to the [make_push_def] of [coIndPreProc.v]; all external push calls
    reference [PushPlain] to stay within the plain push world. *)
Definition make_push_def_plain
    (old_kn        : kername)
    (new_ind       : inductive)
    (n_block       : nat)
    (new_oib       : one_inductive_body)
    (n_old_ctors   : nat)
    (type_map      : list (kername * inductive))
    (app_kn_map    : list (kername * list term * inductive))
    (pi_set        : list kername)
    (is_purely_ind : bool)
    (cur_mp        : modpath)
    : def term :=
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
    | None                => []
    | Some (_, arg_terms) => arg_terms
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
                  if is_purely_ind then
                    tApp (tRel (n_args + 1)) [tRel snoc_i]
                  else
                    tApp (tRel (n_args + 3)) [tRel n_args; tRel snoc_i]
              | Some (Some kn) =>
                  let push_const := tConst (cur_mp, snd kn ++ "PushPlain") [] in
                  if existsb (eq_kername kn) pi_set then
                    tApp push_const [tRel snoc_i]
                  else
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
  let dname := {| binder_name := nNamed (type_nm ++ "PushPlain"); binder_relevance := Relevant |} in
  if is_purely_ind then
    {| dname := dname;
       dtype  := tProd anon_b new_type old_type;
       dbody  := tLambda anon_b new_type (tCase ci pred (tRel 0) branches);
       rarg   := 0 |}
  else
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
    {| dname := dname;
       dtype  := tProd anon_b (tInd nat_ind_ref []) (tProd anon_b new_type old_type);
       dbody  := dbody;
       rarg   := 0 |}.

Polymorphic Fixpoint generate_push_fns_plain
    (todo        : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map     : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (pi_set      : list kername)
    (cur_mp      : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
    tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
            | None =>
              tmFail ("generate_push_fns_plain: no body for " ++ snd old_kn)
            | Some new_oib =>
              let n_old_ctors :=
                match nth_error old_mind.(ind_bodies) 0 with
                | Some ob => List.length ob.(ind_ctors)
                | None    => 0
                end in
              let n_block := List.length new_mind.(ind_bodies) in
              let is_purely_ind := existsb (eq_kername old_kn) pi_set in
              let d := make_push_def_plain old_kn new_ind n_block new_oib n_old_ctors
                                           all_map app_kn_map pi_set is_purely_ind cur_mp in
              push_term_ev <- tmEval all (tFix [d] 0) ;;
              tmMkDefinition (snd old_kn ++ "PushPlain") push_term_ev
            end) (fun _ =>
    generate_push_fns_plain rest all_map app_kn_map pi_set cur_mp)
  end.

(** Build the [def term] entry for the push function of [old_kn] mapping
    the lifted inductive [new_ind] (body [new_oib] in a block with [n_block]
    bodies) back to the original type, returning [HoleyResult old_type].
    For parametric specialisations (e.g. [listnat] is [list nat]), the return
    type and constructor heads use the parametric head ([list]) with params
    applied, mirroring [make_lift_def]'s [orig_form] logic.
    De Bruijn inside a branch with [n_args] args:
      tRel snoc_i     = constructor arg at snoc position [snoc_i]
      tRel n_args     = outer lambda variable (the scrutinee, unused)
      tRel (n_args+1) = the fix/cofix function itself (self-push) *)
Definition make_push_def
    (old_kn        : kername)
    (new_ind       : inductive)
    (n_block       : nat)
    (new_oib       : one_inductive_body)
    (n_old_ctors   : nat)
    (type_map      : list (kername * inductive))
    (app_kn_map    : list (kername * list term * inductive))
    (pi_set        : list kername)
    (is_purely_ind : bool)
    (cur_mp        : modpath)
    (hr_hole_c     : term)
    (hr_pure_c     : term)
    (hr_ap_c       : term)
    (hr_type_c     : term)
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
    | None                => []
    | Some (_, arg_terms) => arg_terms
    end in
  let old_type :=
    match par_terms with
    | [] => tInd head_ind []
    | _  => tApp (tInd head_ind []) par_terms
    end in
  let holey_old_type := tApp hr_type_c [old_type] in
  let new_type     := tInd new_ind [] in
  let type_nm      := snd old_kn in
  let new_kn       := inductive_mind new_ind in
  let body_idx     := inductive_ind new_ind in
  let anon_b       := {| binder_name := nAnon; binder_relevance := Relevant |} in
  (* Push functions return [HoleyResult old_type] instead of [old_type].
     De Bruijn layout is unchanged from the original Push description.

     Original constructor: fold hr_ap over the pushed arguments.
       - Pushed args (Some None / Some (Some kn)) already return HoleyResult.
       - Pass-through args (None) are wrapped with hr_pure.
     Extra constructors (animation / undefined'): return hr_hole old_type.
     Depth-0 branch (non-purely-inductive): return hr_hole old_type. *)
  let branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      let bbody :=
        if Nat.ltb ctor_idx n_old_ctors then
          (* Build (holey_push_term, orig_arg_type) for each arg in snoc order. *)
          let push_and_types_snoc :=
            List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
              | Some None =>
                  let self_push :=
                    if is_purely_ind then
                      tApp (tRel (n_args + 1)) [tRel snoc_i]
                    else
                      tApp (tRel (n_args + 3)) [tRel n_args; tRel snoc_i] in
                  (self_push, old_type)
              | Some (Some kn) =>
                  let push_const := tConst (cur_mp, snd kn ++ "Push") [] in
                  let ext_push :=
                    if existsb (eq_kername kn) pi_set then
                      tApp push_const [tRel snoc_i]
                    else
                      tApp push_const [tRel n_args; tRel snoc_i] in
                  (* For parametric specialisations (e.g. [kn = listnat], the
                     original type is [list nat], not [listnat]).  Recover the
                     head + params via app_kn_map so that B_types uses the same
                     form as the original constructor's signature. *)
                  let kn_ind := {| inductive_mind := kn; inductive_ind := 0 |} in
                  let lifted_for_kn :=
                    match find (fun e => eq_kername (fst e) kn) type_map with
                    | Some (_, ni) => ni
                    | None         => kn_ind
                    end in
                  let orig_arg_t :=
                    match find (fun e =>
                                  andb (eq_kername (inductive_mind (snd e))
                                                   (inductive_mind lifted_for_kn))
                                       (Nat.eqb (inductive_ind (snd e))
                                                (inductive_ind lifted_for_kn)))
                               app_kn_map with
                    | Some ((head_kn, params), _) =>
                        match params with
                        | [] => tInd {| inductive_mind := head_kn; inductive_ind := 0 |} []
                        | _  => tApp (tInd {| inductive_mind := head_kn; inductive_ind := 0 |} []) params
                        end
                    | None => tInd kn_ind []
                    end in
                  (ext_push, orig_arg_t)
              | None =>
                  (tApp hr_pure_c [arg_t; tRel snoc_i], arg_t)
              end)
            (seq 0 n_args) in
          (* Reverse to normal (left-to-right) constructor argument order. *)
          let push_and_types := List.rev push_and_types_snoc in
          let holey_args     := List.map fst push_and_types in
          let orig_arg_types := List.map snd push_and_types in
          (* B_types[i] = orig_arg_types[i] -> ... -> orig_arg_types[n-1] -> old_type.
             B_types[0] is the full constructor type; B_types[n] = old_type. *)
          let B_types :=
            List.fold_right (fun orig_t acc =>
              tProd anon_b orig_t (List.hd old_type acc) :: acc)
            [old_type] orig_arg_types in
          let base_ctor :=
            match par_terms with
            | [] => tConstruct head_ind ctor_idx []
            | _  => tApp (tConstruct head_ind ctor_idx []) par_terms
            end in
          let full_ctor_type := List.hd old_type B_types in
          let init_holey := tApp hr_pure_c [full_ctor_type; base_ctor] in
          (* Fold: apply each holey arg via hr_ap, consuming one B_type per step. *)
          fst (List.fold_left
            (fun '(current, b_list) '(holey_arg, orig_t) =>
              match b_list with
              | _ :: b_rest =>
                  let b_next := List.hd old_type b_rest in
                  (tApp hr_ap_c [orig_t; b_next; current; holey_arg], b_rest)
              | [] => (current, [])
              end)
            (List.combine holey_args orig_arg_types)
            (init_holey, B_types))
        else
          tApp hr_hole_c [old_type]
      in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    new_oib.(ind_ctors) in
  let pred  := {| puinst := []; pparams := [];
                  pcontext := [anon_b];
                  preturn  := holey_old_type |} in
  let ci    := {| ci_ind := new_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let dname := {| binder_name := nNamed (type_nm ++ "Push"); binder_relevance := Relevant |} in
  if is_purely_ind then
    {| dname := dname;
       dtype  := tProd anon_b new_type holey_old_type;
       dbody  := tLambda anon_b new_type (tCase ci pred (tRel 0) branches);
       rarg   := 0 |}
  else
    let nat_ind_ref := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
    let nat_ci   := {| ci_ind := nat_ind_ref; ci_npar := 0; ci_relevance := Relevant |} in
    let nat_pred := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := holey_old_type |} in
    let inner_case := tCase ci pred (tRel 1) branches in
    let o_branch   := {| bcontext := [];       bbody := tApp hr_hole_c [old_type] |} in
    let s_branch   := {| bcontext := [anon_b]; bbody := inner_case     |} in
    let dbody :=
      tLambda anon_b (tInd nat_ind_ref [])
        (tLambda anon_b new_type
          (tCase nat_ci nat_pred (tRel 1) [o_branch; s_branch])) in
    {| dname := dname;
       dtype  := tProd anon_b (tInd nat_ind_ref []) (tProd anon_b new_type holey_old_type);
       dbody  := dbody;
       rarg   := 0 |}.

(** One fixed-point step for computing the not-purely-inductive set.
    A type is not purely inductive if it is coinductive, or if any of its
    constructor-arg types that are in [all_map] are themselves not purely
    inductive.  Returns [(updated_npi_set, changed)]. *)
Polymorphic Fixpoint compute_npi_step
    (todo    : list (kername * inductive))
    (all_map : list (kername * inductive))
    (npi_set : list kername)
    (changed : bool)
    : TemplateMonad (list kername * bool) :=
  match todo with
  | [] => tmReturn (npi_set, changed)
  | (old_kn, _) :: rest =>
    if existsb (eq_kername old_kn) npi_set
    then compute_npi_step rest all_map npi_set changed
    else
      tmBind (tmQuoteInductive old_kn) (fun old_mind =>
      let is_coind :=
        match old_mind.(ind_finite) with CoFinite => true | _ => false end in
      if is_coind
      then compute_npi_step rest all_map (npi_set ++ [old_kn]) true
      else
        let ctor_kns :=
          dedup_kns (flat_map (fun oib =>
            flat_map (fun c => collect_tind_kns c.(cstr_type))
                     oib.(ind_ctors))
            old_mind.(ind_bodies)) in
        let in_map_npi :=
          existsb (fun kn =>
            andb (existsb (fun e => eq_kername (fst e) kn) all_map)
                 (existsb (eq_kername kn) npi_set))
            ctor_kns in
        if in_map_npi
        then compute_npi_step rest all_map (npi_set ++ [old_kn]) true
        else compute_npi_step rest all_map npi_set changed)
  end.

(** Iterate [compute_npi_step] until the not-purely-inductive set stabilises.
    Fuel = |type_mapping| + 1 is a tight upper bound: npi_set can grow by at
    most one element per changed-pass, so at most |type_mapping| changed-passes
    occur before convergence, plus one final unchanged-pass.  The 0 branch is
    therefore dead code; tmFail there is a defensive guard. *)
Polymorphic Fixpoint compute_npi_fix
    (all_map : list (kername * inductive))
    (npi_set : list kername)
    (fuel    : nat)
    : TemplateMonad (list kername) :=
  match fuel with
  | 0 =>
    tmFail ("compute_npi_fix: did not converge after " ++
            string_of_nat (List.length all_map + 1) ++
            " passes; not-purely-inductive set so far: " ++
            String.concat ", " (List.map snd npi_set))
  | S f =>
    tmBind (compute_npi_step all_map all_map npi_set false) (fun res =>
    if snd res
    then compute_npi_fix all_map (fst res) f
    else tmReturn (fst res))
  end.

(** Declare a push function for every type in [todo].
    Purely-inductive types (no transitive coinductive dependency) get a simple
    structural fix with no depth parameter.  Types with coinductive deps keep
    the depth-bounded form used previously. *)
Polymorphic Fixpoint generate_push_fns
    (todo        : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map     : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (pi_set      : list kername)
    (cur_mp      : modpath)
    (hr_hole_c   : term)
    (hr_pure_c   : term)
    (hr_ap_c     : term)
    (hr_type_c   : term)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
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
              let is_purely_ind := existsb (eq_kername old_kn) pi_set in
              let d := make_push_def old_kn new_ind n_block new_oib n_old_ctors
                                     all_map app_kn_map pi_set is_purely_ind cur_mp
                                     hr_hole_c hr_pure_c hr_ap_c hr_type_c in
              push_term_ev <- tmEval all (tFix [d] 0) ;;
              tmMkDefinition (snd old_kn ++ "Push") push_term_ev
            end) (fun _ =>
    generate_push_fns rest all_map app_kn_map pi_set cur_mp
                      hr_hole_c hr_pure_c hr_ap_c hr_type_c)
  end.

(* ------------------------------------------------------------------ *)
(** ** ChkNoExtraCstrs function generation                            *)
(* ------------------------------------------------------------------ *)

(** Build the [def term] for the [ChkNoExtraCstrs] fixpoint of [old_kn].
    The function maps every term of the lifted type [new_ind] to [bool]:
    - Original (primed) constructors recurse on args that belong to the
      lifting set and AND the results; all other args are ignored.
    - Any extra constructor (animation or UndefinedCstr) returns [false].
    De Bruijn inside a branch with [n_args] binders:
      tRel 0..n_args-1  = constructor args (snoc order)
      tRel n_args       = outer lambda variable (scrutinee, unused)
      tRel (n_args+1)   = the fix itself *)
Definition make_chk_def
    (old_kn      : kername)
    (new_ind     : inductive)
    (n_block     : nat)
    (new_oib     : one_inductive_body)
    (n_old_ctors : nat)
    (type_map    : list (kername * inductive))
    (cur_mp      : modpath)
    : def term :=
  let type_nm  := snd old_kn in
  let new_type := tInd new_ind [] in
  let new_kn   := inductive_mind new_ind in
  let body_idx := inductive_ind new_ind in
  let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let bool_ind := {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "bool");
                     inductive_ind  := 0 |} in
  let bool_t  := tInd bool_ind [] in
  let true_t  := tConstruct bool_ind 0 [] in
  let false_t := tConstruct bool_ind 1 [] in
  let andb_kn := (MPfile ["Datatypes"; "Init"; "Corelib"], "andb") in
  let fold_andb chks :=
    match chks with
    | []  => true_t
    | [c] => c
    | _   => List.fold_right (fun c acc => tApp (tConst andb_kn []) [c; acc]) true_t chks
    end in
  let branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      let bbody :=
        if Nat.ltb ctor_idx n_old_ctors then
          let chk_terms :=
            List.concat (List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
              | Some None         => [tApp (tRel (n_args + 1)) [tRel snoc_i]]
              | Some (Some kn)    => [tApp (tConst (cur_mp, snd kn ++ "ChkNoExtraCstrs") [])
                                           [tRel snoc_i]]
              | None              => []
              end)
              (seq 0 n_args)) in
          fold_andb chk_terms
        else
          false_t
      in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    new_oib.(ind_ctors) in
  let pred  := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := bool_t |} in
  let ci    := {| ci_ind := new_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let dname := {| binder_name    := nNamed (type_nm ++ "ChkNoExtraCstrs");
                  binder_relevance := Relevant |} in
  {| dname := dname;
     dtype  := tProd anon_b new_type bool_t;
     dbody  := tLambda anon_b new_type (tCase ci pred (tRel 0) branches);
     rarg   := 0 |}.

(** Declare a [ChkNoExtraCstrs] function for every purely-inductive type in
    [todo].  Non-purely-inductive entries are silently skipped. *)
Polymorphic Fixpoint generate_chk_fns
    (todo    : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map : list (kername * inductive))
    (pi_set  : list kername)
    (cur_mp  : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
    if negb (existsb (eq_kername old_kn) pi_set)
    then generate_chk_fns rest all_map pi_set cur_mp
    else
      tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
              | None =>
                tmFail ("generate_chk_fns: no body for " ++ snd old_kn)
              | Some new_oib =>
                let n_old_ctors :=
                  match nth_error old_mind.(ind_bodies) 0 with
                  | Some ob => List.length ob.(ind_ctors)
                  | None    => 0
                  end in
                let n_block := List.length new_mind.(ind_bodies) in
                let d := make_chk_def old_kn new_ind n_block new_oib n_old_ctors all_map cur_mp in
                chk_term_ev <- tmEval all (tFix [d] 0) ;;
                tmMkDefinition (snd old_kn ++ "ChkNoExtraCstrs") chk_term_ev
              end) (fun _ =>
      generate_chk_fns rest all_map pi_set cur_mp)
  end.

(* ------------------------------------------------------------------ *)
(** ** Equality function generation (eqFn<T>') for lifted types       *)
(* ------------------------------------------------------------------ *)

(** Build the [def term] for the structural equality fixpoint of
    lifted type [new_ind].  The function has type [T' -> T' -> bool]:
    - Matching original (primed) constructors: AND together per-arg
      comparisons (recursive call for self-refs, cross-type eqFn for
      other tracked types, ignored for untracked args).
    - Mismatched original constructors → [false].
    - Any extra or UndefinedCstr constructor → [false].
    De Bruijn inside outer match branch with [n_args] binders:
      tRel 0..n_args-1    = a's ctor args (snoc)
      tRel n_args         = b (outer λ, shifted)
      tRel n_args+1       = a (outer λ, shifted)
      tRel n_args+2       = fix
    Inside inner match (same ctor, [n_args] more binders):
      tRel 0..n_args-1    = b's ctor args (snoc)
      tRel n_args+snoc_i  = a's ctor arg [snoc_i]
      tRel 2*n_args+2     = fix *)
Definition make_eqfn_def
    (old_kn      : kername)
    (new_ind     : inductive)
    (n_block     : nat)
    (new_oib     : one_inductive_body)
    (n_old_ctors : nat)
    (type_map    : list (kername * inductive))
    (cur_mp      : modpath)
    : def term :=
  let type_nm  := snd old_kn in
  let new_type := tInd new_ind [] in
  let new_kn   := inductive_mind new_ind in
  let body_idx := inductive_ind new_ind in
  let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let bool_ind := {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "bool");
                     inductive_ind  := 0 |} in
  let bool_t  := tInd bool_ind [] in
  let true_t  := tConstruct bool_ind 0 [] in
  let false_t := tConstruct bool_ind 1 [] in
  let andb_kn := (MPfile ["Datatypes"; "Init"; "Corelib"], "andb") in
  let fold_andb chks :=
    match chks with
    | []  => true_t
    | [c] => c
    | _   => List.fold_right (fun c acc => tApp (tConst andb_kn []) [c; acc]) true_t chks
    end in
  let ci   := {| ci_ind := new_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let pred := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := bool_t |} in
  (* Outer match branches on [a]. *)
  let outer_branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      let bbody :=
        if Nat.ltb ctor_idx n_old_ctors then
          (* Inner match on [b = tRel n_args]. *)
          let inner_branches :=
            mapi (fun inner_idx inner_ctor =>
              let inner_body :=
                if Nat.eqb inner_idx ctor_idx then
                  (* Same constructor: compare args pairwise. *)
                  let cmp_terms :=
                    List.concat (List.map (fun snoc_i =>
                      let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                                   | Some d => d.(decl_type) | None => tVar "?" end in
                      match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
                      | Some None      =>
                          (* Self-ref: recursive eqFn call. *)
                          [tApp (tRel (n_args + n_args + 2))
                                [tRel (n_args + snoc_i); tRel snoc_i]]
                      | Some (Some kn) =>
                          (* Cross-type: call eqFn with block-kname + body-idx naming. *)
                          let cross_fn_nm :=
                            match find (fun e => eq_kername (fst e) kn) type_map with
                            | Some (_, ci) =>
                              let blk := snd (inductive_mind ci) in
                              let cj  := inductive_ind ci in
                              if Nat.eqb cj 0 then "eqFn" ++ blk
                              else "eqFn" ++ blk ++ "_" ++ string_of_nat cj
                            | None => "eqFn" ++ snd kn ++ "'"
                            end in
                          [tApp (tConst (cur_mp, cross_fn_nm) [])
                                [tRel (n_args + snoc_i); tRel snoc_i]]
                      | None           =>
                          (* Not a self-ref or cross-lifted-type.  Ask type_to_eq_fn;
                             it returns the tConstruct for [false] when the type is
                             unsupported, and a usable function otherwise. *)
                          let eq_fn := type_to_eq_fn arg_t in
                          match eq_fn with
                          | tConstruct _ _ _ => [false_t]
                          | _ => [tApp eq_fn [tRel (n_args + snoc_i); tRel snoc_i]]
                          end
                      end)
                      (seq 0 n_args)) in
                  fold_andb cmp_terms
                else
                  false_t
              in
              {| bcontext := List.rev (List.map (fun d => d.(decl_name)) inner_ctor.(cstr_args));
                 bbody    := inner_body |})
            new_oib.(ind_ctors) in
          tCase ci pred (tRel n_args) inner_branches
        else
          false_t
      in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    new_oib.(ind_ctors) in
  (* Name the fix binder to match [type_to_eq_fn]'s naming scheme:
     "eqFn" ++ block_kname for ind=0, "eqFn" ++ block_kname ++ "_" ++ j for ind>0. *)
  let fix_nm :=
    let blk := snd new_kn in
    if Nat.eqb body_idx 0 then "eqFn" ++ blk
    else "eqFn" ++ blk ++ "_" ++ string_of_nat body_idx in
  let dname := {| binder_name    := nNamed fix_nm;
                  binder_relevance := Relevant |} in
  (* Outer fix has rarg=0 (decreases on first arg [a]). *)
  {| dname := dname;
     dtype  := tProd anon_b new_type (tProd anon_b new_type bool_t);
     dbody  := tLambda anon_b new_type
                 (tLambda anon_b new_type
                   (tCase ci pred (tRel 1) outer_branches));
     rarg   := 0 |}.

(** Declare an [eqFn<T>'] function for every purely-inductive type in
    [todo].  Non-purely-inductive entries are silently skipped.
    For types at body index 0 the name is ["eqFn" ++ block_kname]; for
    bodies at index [j > 0] the name is ["eqFn" ++ block_kname ++ "_" ++ j].
    This matches what [EqualityResolution.type_to_eq_fn] generates. *)
Polymorphic Fixpoint generate_eqfn_defs
    (todo    : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map : list (kername * inductive))
    (pi_set  : list kername)
    (cur_mp  : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
    if negb (existsb (eq_kername old_kn) pi_set)
    then generate_eqfn_defs rest all_map pi_set cur_mp
    else
      tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
              | None =>
                tmFail ("generate_eqfn_defs: no body for " ++ snd old_kn)
              | Some new_oib =>
                let n_old_ctors :=
                  match nth_error old_mind.(ind_bodies) 0 with
                  | Some ob => List.length ob.(ind_ctors)
                  | None    => 0
                  end in
                let n_block := List.length new_mind.(ind_bodies) in
                let d := make_eqfn_def old_kn new_ind n_block new_oib n_old_ctors all_map cur_mp in
                (* Name matches type_to_eq_fn's naming: "eqFn"++block_nm (for ind=0)
                   or "eqFn"++block_nm++"_"++j (for ind>0). *)
                let blk_nm := snd (inductive_mind new_ind) in
                let body_j := inductive_ind new_ind in
                let fn_nm :=
                  if Nat.eqb body_j 0 then "eqFn" ++ blk_nm
                  else "eqFn" ++ blk_nm ++ "_" ++ string_of_nat body_j in
                eqfn_term_ev <- tmEval all (tFix [d] 0) ;;
                tmMkDefinition fn_nm eqfn_term_ev
              end) (fun _ =>
      generate_eqfn_defs rest all_map pi_set cur_mp)
  end.

(* ------------------------------------------------------------------ *)
(** ** Lifted premise-function generation                             *)
(* ------------------------------------------------------------------ *)

(** For each premise function [fn_kn] (collected from ctor equality premises),
    declare [fn_kn_liftedFunc] that:
    - If any input is lifted: checks [ChkNoExtraCstrs] on every lifted input;
      if any has extra ctors returns [undefinedCstr] of the lifted output type,
      otherwise pushes every lifted input, applies the original function, and
      lifts the output.
    - If only the output is lifted: applies the original function and lifts the
      output.
    - If neither input nor output is lifted: defines an alias for the original
      function.
    Assumption: all input and output types of [fn_kn] are pure inductives. *)
Polymorphic Fixpoint generate_lifted_fns
    (fn_infos   : list (kername * list term * term))
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (cur_mp     : modpath)
    : TemplateMonad unit :=
  match fn_infos with
  | [] => tmReturn tt
  | fn_info :: rest =>
    let fn_kn     := fst (fst fn_info) in
    let arg_types := snd (fst fn_info) in
    let ret_type  := snd fn_info in
    let n         := List.length arg_types in
    let anon_b    := {| binder_name := nAnon; binder_relevance := Relevant |} in
    let bool_ind  := {| inductive_mind :=
                          (MPfile ["Datatypes"; "Init"; "Corelib"], "bool");
                        inductive_ind := 0 |} in
    let true_t    := tConstruct bool_ind 0 [] in
    let andb_kn   := (MPfile ["Datatypes"; "Init"; "Corelib"], "andb") in
    let fold_andb chks :=
      match chks with
      | []  => true_t
      | [c] => c
      | _   => List.fold_right
                 (fun c acc => tApp (tConst andb_kn []) [c; acc]) true_t chks
      end in
    (* resolve_tp: given a type term, return Some (old_kn, new_ind) if lifted *)
    let resolve_tp (tp : term) : option (kername * inductive) :=
      match tp with
      | tInd ind _ =>
        let kn := inductive_mind ind in
        match find (fun e => eq_kername (fst e) kn) type_map with
        | Some entry => Some entry
        | None      => None
        end
      | tApp (tInd head_ind _) arg_terms =>
        let kn := inductive_mind head_ind in
        if negb (forallb is_ind_type arg_terms) then None
        else
          match find (fun e =>
            andb (eq_kername (fst (fst e)) kn)
                 (andb (Nat.eqb #|snd (fst e)| #|arg_terms|)
                       (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                                (combine (snd (fst e)) arg_terms))))
            app_kn_map with
          | Some (_, new_ind) =>
            match find (fun e =>
              andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                   (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
              type_map with
            | Some entry => Some entry
            | None      => None
            end
          | None => None
          end
      | _ => None
      end in
    let arg_infos := List.map resolve_tp arg_types in
    let ret_info  := resolve_tp ret_type in
    let any_input_lifted :=
      existsb (fun o => match o with Some _ => true | None => false end)
              arg_infos in
    (* lambda binder types: use lifted type if arg is lifted, original otherwise *)
    let lifted_arg_types :=
      List.map (fun pair =>
        match fst pair with
        | Some (_, new_ind) => tInd new_ind []
        | None              => snd pair
        end) (combine arg_infos arg_types) in
    (* inside n lambdas, arg i (0-indexed from outermost) = tRel (n-1-i) *)
    let pushed_args :=
      mapi (fun i info =>
        let rel_i := tRel (n - 1 - i) in
        match info with
        | Some (old_kn, _) =>
          tApp (tConst (cur_mp, snd old_kn ++ "PushPlain") []) [rel_i]
        | None => rel_i
        end) arg_infos in
    let f_applied :=
      match pushed_args with
      | [] => tConst fn_kn []
      | _  => tApp (tConst fn_kn []) pushed_args
      end in
    let chk_terms :=
      flat_map (fun p =>
        match snd p with
        | Some (old_kn, _) =>
          let rel_i := tRel (n - 1 - fst p) in
          [tApp (tConst (cur_mp, snd old_kn ++ "ChkNoExtraCstrs") []) [rel_i]]
        | None => []
        end) (mapi (fun i info => (i, info)) arg_infos) in
    let all_good := fold_andb chk_terms in
    tmBind
      (match any_input_lifted, ret_info with
       | true, Some (ret_old_kn, new_ret_ind) =>
         tmBind (tmQuoteInductive (inductive_mind new_ret_ind)) (fun lifted_ret_mind =>
           let lifted_ret_ctors :=
             match nth_error lifted_ret_mind.(ind_bodies) (inductive_ind new_ret_ind) with
             | Some ob => ob.(ind_ctors)
             | None    => []
             end in
           let ctor_nm := snd fn_kn ++ "LiftedCstr" in
           let all_inputs := List.map (fun i => tRel (n - 1 - i)) (seq 0 n) in
           let lifted_cstr_out :=
             match find_ctor_idx ctor_nm lifted_ret_ctors 0 with
             | Some idx => tApp (tConstruct new_ret_ind idx []) all_inputs
             | None     => tConstruct new_ret_ind 0 []
             end in
           let lifted_out :=
             tApp (tConst (cur_mp, snd ret_old_kn ++ "Lift") []) [f_applied] in
           let bool_ci   :=
             {| ci_ind := bool_ind; ci_npar := 0; ci_relevance := Relevant |} in
           let bool_pred :=
             {| puinst := []; pparams := []; pcontext := [anon_b];
                preturn := tInd new_ret_ind [] |} in
           let body := tCase bool_ci bool_pred all_good
             [{| bcontext := []; bbody := lifted_out      |};
              {| bcontext := []; bbody := lifted_cstr_out |}] in
           let fn_term :=
             List.fold_right
               (fun tp acc => tLambda anon_b tp acc) body lifted_arg_types in
           fn_term_ev <- tmEval all fn_term ;;
           tmMkDefinition (snd fn_kn ++ "liftedFunc") fn_term_ev)
       | true, None =>
         let fn_term :=
           List.fold_right
             (fun tp acc => tLambda anon_b tp acc) f_applied lifted_arg_types in
         fn_term_ev <- tmEval all fn_term ;;
         tmMkDefinition (snd fn_kn ++ "liftedFunc") fn_term_ev
       | false, Some (ret_old_kn, _) =>
         let lift_fn := tConst (cur_mp, snd ret_old_kn ++ "Lift") [] in
         let body    := tApp lift_fn [f_applied] in
         let fn_term :=
           List.fold_right
             (fun tp acc => tLambda anon_b tp acc) body lifted_arg_types in
         fn_term_ev <- tmEval all fn_term ;;
         tmMkDefinition (snd fn_kn ++ "liftedFunc") fn_term_ev
       | false, None =>
         fn_term_ev <- tmEval all (tConst fn_kn []) ;;
         tmMkDefinition (snd fn_kn ++ "liftedFunc") fn_term_ev
       end) (fun _ =>
    generate_lifted_fns rest type_map app_kn_map cur_mp)
  end.

(* ------------------------------------------------------------------ *)
(** ** InputLift function generation                                  *)
(* ------------------------------------------------------------------ *)

(** Given an original type term, return [(lifted_type, Some lift_fn)] if
    the type is tracked in [type_map]/[app_kn_map], or [(t, None)] if not. *)
Definition classify_in_type
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
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
    let kn := inductive_mind ind in
    let found :=
      if negb (forallb is_ind_type args) then None
      else
        find (fun e =>
                andb (eq_kername (fst (fst e)) kn)
                     (andb (Nat.eqb #|snd (fst e)| #|args|)
                           (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                                    (combine (snd (fst e)) args))))
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
    (todo        : list (inductive * (string * (list nat * list nat))))
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (prod_kn     : kername)
    (anim_res_kn : kername)
    (cur_mp      : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let block_kn := inductive_mind (fst entry) in
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
      fn_term_ev <- tmEval all fn_term ;;
      tmBind (tmMkDefinition (rel_name ++ "inputLift") fn_term_ev) (fun _ =>
      generate_inputLift_fns rest type_map app_kn_map prod_kn anim_res_kn cur_mp)
    end)
  end.

(* ------------------------------------------------------------------ *)
(** ** OutputPush function generation                                  *)
(* ------------------------------------------------------------------ *)

(** Given an original output type term, return [(lifted_type, Some (push_fn, is_pi))]
    if the type is tracked in [type_map]/[app_kn_map], or [(t, None)] if not.
    [is_pi] is true when the push function takes no [nat] depth argument (purely inductive). *)
Definition classify_out_type
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (pi_set     : list kername)
    (cur_mp     : modpath)
    (t          : term)
    : term * option (term * bool) :=
  match t with
  | tInd ind _ =>
    let kn := inductive_mind ind in
    match find (fun e => eq_kername (fst e) kn) type_map with
    | Some (old_kn, new_ind) =>
      let is_pi := existsb (eq_kername old_kn) pi_set in
      (tInd new_ind [], Some (tConst (cur_mp, snd old_kn ++ "Push") [], is_pi))
    | None => (t, None)
    end
  | tApp (tInd ind _) args =>
    let kn := inductive_mind ind in
    let found :=
      if negb (forallb is_ind_type args) then None
      else
        find (fun e =>
                andb (eq_kername (fst (fst e)) kn)
                     (andb (Nat.eqb #|snd (fst e)| #|args|)
                           (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                                    (combine (snd (fst e)) args))))
             app_kn_map in
    match found with
    | Some (_, new_ind) =>
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 type_map with
      | Some (old_kn, _) =>
        let is_pi := existsb (eq_kername old_kn) pi_set in
        (tInd new_ind [], Some (tConst (cur_mp, snd old_kn ++ "Push") [], is_pi))
      | None => (t, None)
      end
    | None => (t, None)
    end
  | _ => (t, None)
  end.

(** Build the raw term for [<rel_name>outputPush]:
      fun (d : nat) out => match out with
                           | Success v => Success orig (apply pushes to v)
                           | _         => NoMatch orig
                           end
    [d] is threaded only to push functions that take a depth argument.
    Purely-inductive push functions (is_pi = true) are applied without [d].
    [orig_types]   : original types at output positions
    [lifted_types] : corresponding lifted types (input to this function)
    [push_fns]     : [Some (fn, is_pi)] or [None] per output *)
Fixpoint build_holey_pair_term (hr_pair_c : term) (prod_kn : kername)
    (types vals : list term) : term :=
  match types, vals with
  | [_],     [v]      => v
  | t :: ts, v :: vs  =>
      let rest_type := make_prod_type prod_kn ts in
      tApp hr_pair_c [t; rest_type; v; build_holey_pair_term hr_pair_c prod_kn ts vs]
  | _,        _       => List.hd (tVar "?") vals
  end.

Definition make_outputPush_term
    (prod_kn      : kername)
    (anim_res_kn  : kername)
    (orig_types   : list term)
    (lifted_types : list term)
    (push_fns     : list (option (term * bool)))
    (hr_type_c    : term)
    (hr_pair_c    : term)
    (hr_pure_c    : term)
    : term :=
  let anim_res_ind  := {| inductive_mind := anim_res_kn; inductive_ind := 0 |} in
  let nat_ind_ref   := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
  let anon_b        := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let lifted_type   := match lifted_types with [t] => t | _ => make_prod_type prod_kn lifted_types end in
  let orig_type     := match orig_types   with [t] => t | _ => make_prod_type prod_kn orig_types   end in
  let holey_orig_type := tApp hr_type_c [orig_type] in
  let anim_in_type  := tApp (tInd anim_res_ind []) [lifted_type] in
  let anim_out_type := tApp (tInd anim_res_ind []) [holey_orig_type] in
  let n_in          := List.length lifted_types in
  (* Depth variable inside the success branch body.
     Binder stack above the depth_var (inside the Success branch):
       1 (anim_res lambda) + 1 (Success branch binder) + 2*(n_in-1) (pair-match binders) = 2*n_in.
     For n_in=1: 1 + 1 = 2 = 2*1.  depth_var = tRel (2*n_in). *)
  let depth_var     := tRel (2 * n_in) in
  let no_match_body := tApp (tConstruct anim_res_ind 2 []) [holey_orig_type] in
  (* Push functions now return HoleyResult T; non-lifted outputs are wrapped
     in hr_pure so every element of pushed_vals is a HoleyResult term. *)
  let pushed_vals :=
    mapi (fun i pfb =>
      match pfb with
      | Some (fn, true)  => tApp fn [input_var i n_in]
      | Some (fn, false) => tApp fn [depth_var; input_var i n_in]
      | None             => tApp hr_pure_c [nth i orig_types (tVar "?"); input_var i n_in]
      end)
    push_fns in
  let pushed_val    := build_holey_pair_term hr_pair_c prod_kn orig_types pushed_vals in
  let success_inner := tApp (tConstruct anim_res_ind 1 []) [holey_orig_type; pushed_val] in
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
    (todo        : list (inductive * (string * (list nat * list nat))))
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (pi_set      : list kername)
    (prod_kn     : kername)
    (anim_res_kn : kername)
    (cur_mp      : modpath)
    (hr_type_c   : term)
    (hr_pair_c   : term)
    (hr_pure_c   : term)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let block_kn := inductive_mind (fst entry) in
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
      let classified   := List.map (classify_out_type type_map app_kn_map pi_set cur_mp) orig_types in
      let lifted_types := List.map fst classified in
      let push_fns     := List.map snd classified in
      let fn_term := make_outputPush_term prod_kn anim_res_kn orig_types lifted_types push_fns
                                          hr_type_c hr_pair_c hr_pure_c in
      fn_term_ev <- tmEval all fn_term ;;
      tmBind (tmMkDefinition (rel_name ++ "outputPush") fn_term_ev) (fun _ =>
      generate_outputPush_fns rest type_map app_kn_map pi_set prod_kn anim_res_kn cur_mp
                               hr_type_c hr_pair_c hr_pure_c)
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
    lift_relation (inductive_mind rel_ind) [] type_mapping [] modes []
  | _ => @tmFail unit "lift_relation_names: failed to resolve knames"
  end.

(** Combined entry point: lift all coinductive types referenced by [modes]
    and then lift the relation itself, in a single [MetaRocq Run].
    [rel_nm] : short name of the top-level relation (e.g. "Integrate").
    [modes]  : input/output positions for every body of the mutual block. *)
Unset Universe Checking.
Polymorphic Definition lift_coinductive_relation
    (modes       : mode_map)
    (fuel        : nat)
    : TemplateMonad unit :=
  (* Resolve every mode entry to its mutual-block kname, in order. *)
  kn_mode_list <- monad_fold_left (fun acc me =>
    refs <- tmLocate (fst me) ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [(ind, me)])
    | _ => tmFail ("lift_coinductive_relation: cannot find '" ++ fst me ++ "'")
    end)
    modes [] ;;
  match kn_mode_list return TemplateMonad unit with
  | [] => @tmFail unit "lift_coinductive_relation: no modes provided"
  | _  =>
    preproc_result <- preprocess_coind_types modes fuel ;;
    preproc_result <- tmEval all preproc_result ;;
    let type_mapping   := fst preproc_result in
    let app_kn_mapping := snd preproc_result in
    cur_mp <- tmCurrentModPath tt ;;
    (* Deduplicate block knames, preserving order of first appearance. *)
    let unique_block_kns :=
      fold_left (fun acc p =>
        if existsb (eq_kername (inductive_mind (fst p))) acc then acc
        else List.app acc [inductive_mind (fst p)])
      kn_mode_list [] in
    (* Pre-compute new inductives for all relation blocks so cross-block references
       in constructor types are substituted correctly when lifting each block. *)
    let rel_mapping :=
      List.map (fun kn =>
        (kn, {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |}))
        unique_block_kns in
    _ <- generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp ;;
    _ <- generate_fnSymb_params type_mapping type_mapping app_kn_mapping ;;
    (* Sort relation blocks so each block is declared only after the blocks
       whose relations appear in its constructor types.  This is necessary when
       blocks are declared with separate [Inductive] commands (e.g. [isZero]
       and [Len]): if [Len'] references [isZero'], [isZero'] must be in the
       environment first. *)
    rel_block_minds_assoc <- monad_map (fun kn =>
      mind <- tmQuoteInductive kn ;;
      tmReturn (kn, mind))
      unique_block_kns ;;
    rel_block_minds_assoc <- tmEval all rel_block_minds_assoc ;;
    let block_id_map := List.map (fun kn => (kn, kn)) unique_block_kns in
    let sorted_block_kns :=
      topo_sort_kns unique_block_kns rel_block_minds_assoc block_id_map
                    [] [] (S #|unique_block_kns|) in
    prod_refs <- tmLocate "prod" ;;
    anim_refs <- tmLocate "animation_result" ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) prod_refs,
          find (fun g => match g with IndRef _ => true | _ => false end) anim_refs with
    | Some (IndRef prod_ind), Some (IndRef anim_ind) =>
      let prod_kn     := inductive_mind prod_ind in
      let anim_res_kn := inductive_mind anim_ind in
      (* generate_push_params, Push, Chk, eqFn, and liftedFunc definitions all
         depend only on the lifted data types (already declared by
         preprocess_coind_types) and are independent of the lifted relation.
         We declare them BEFORE lift_relation so that [substliftedFunc] (and
         other liftedFuncs) already exist when the lifted relation ctor types
         that reference them are type-checked by tmMkInductive. *)
      _ <- generate_push_params type_mapping type_mapping app_kn_mapping ;;
      npi_set <- compute_npi_fix type_mapping [] (List.length type_mapping + 1) ;;
      npi_set <- tmEval all npi_set ;;
      let pi_set :=
        List.map fst (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set)) type_mapping) in
      type_minds <- monad_map (fun entry =>
        old_mind <- tmQuoteInductive (fst entry) ;;
        new_mind <- tmQuoteInductive (inductive_mind (snd entry)) ;;
        tmReturn (entry, (old_mind, new_mind)))
        type_mapping ;;
      type_minds <- tmEval all type_minds ;;
      hr_hole_tm  <- tmQuote (hr_hole) ;;
      hr_pure_tm  <- tmQuote (hr_pure) ;;
      hr_ap_tm    <- tmQuote (hr_ap) ;;
      hr_type_tm  <- tmQuote (HoleyResult) ;;
      hr_pair_tm  <- tmQuote (hr_pair) ;;
      _ <- generate_push_fns_plain type_minds type_mapping app_kn_mapping pi_set cur_mp ;;
      _ <- generate_push_fns type_minds type_mapping app_kn_mapping pi_set cur_mp
                              hr_hole_tm hr_pure_tm hr_ap_tm hr_type_tm ;;
      _ <- generate_chk_fns type_minds type_mapping pi_set cur_mp ;;
      _ <- generate_eqfn_defs type_minds type_mapping pi_set cur_mp ;;
      let all_fn_infos_base :=
        flat_map (fun km =>
          let n_params := (snd km).(ind_npars) in
          flat_map (fun oib =>
            let idx_types := extract_arg_types n_params 100 oib.(ind_type) in
            flat_map (fun c =>
              collect_fn_app_info_from_ctor idx_types rel_block_minds_assoc c)
                     oib.(ind_ctors))
          (snd km).(ind_bodies))
        rel_block_minds_assoc in
      let unique_fn_infos_base :=
        fold_left (fun acc entry =>
          let fkn := fst (fst entry) in
          if existsb (fun e => eq_kername (fst (fst e)) fkn) acc
          then acc
          else List.app acc [entry])
        all_fn_infos_base [] in
      unique_fn_infos_base <- tmEval all unique_fn_infos_base ;;
      (* Also pick up function applications nested inside constructor applications
         in index terms (e.g. [Nat.add m n] inside [Seq (m+n) s2]).  Look up
         the return type for any new fn_kn via tmQuoteConstant. *)
      let extra_fn_pairs_r :=
        flat_map (fun km =>
          flat_map (fun oib =>
            flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
          (snd km).(ind_bodies))
        rel_block_minds_assoc in
      let new_fn_pairs_r :=
        fold_left (fun acc p =>
          let fn_kn := fst p in
          if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) unique_fn_infos_base)
                 (existsb (fun q => eq_kername (fst q) fn_kn) acc)
          then acc
          else List.app acc [p])
        extra_fn_pairs_r [] in
      new_fn_pairs_r <- tmEval all new_fn_pairs_r ;;
      extra_fn_infos_r <- monad_map (fun p =>
        let fn_kn := fst p in
        let n     := List.length (snd p) in
        cb <- tmQuoteConstant fn_kn false ;;
        let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
        tmReturn (fn_kn, decl_arg_types, ret_tp)) new_fn_pairs_r ;;
      extra_fn_infos_r <- tmEval all extra_fn_infos_r ;;
      let unique_fn_infos := List.app unique_fn_infos_base extra_fn_infos_r in
      unique_fn_infos <- tmEval all unique_fn_infos ;;
      _ <- generate_lifted_fns unique_fn_infos type_mapping app_kn_mapping cur_mp ;;
      (* Build fn_kn_map from unique_fn_infos: every function that has a liftedFunc
         definition maps old_kn → (cur_mp, name ++ "liftedFunc"). *)
      let fn_kn_map :=
        List.map (fun fi => (fst (fst fi), (cur_mp, snd (fst (fst fi)) ++ "liftedFunc")))
                 unique_fn_infos in
      (* Now all liftedFunc constants exist; declare the lifted relation blocks. *)
      _ <- monad_fold_left (fun _ block_kn =>
        let block_modes :=
          List.map snd (filter (fun p => eq_kername (inductive_mind (fst p)) block_kn) kn_mode_list) in
        lift_relation block_kn rel_mapping type_mapping app_kn_mapping block_modes fn_kn_map)
        sorted_block_kns tt ;;
      _ <- generate_inputLift_fns kn_mode_list type_mapping app_kn_mapping
                                   prod_kn anim_res_kn cur_mp ;;
      _ <- generate_rest_fns kn_mode_list cur_mp prod_kn ;;
      generate_outputPush_fns kn_mode_list type_mapping app_kn_mapping pi_set
                              prod_kn anim_res_kn cur_mp
                              hr_type_tm hr_pair_tm hr_pure_tm
    | _, _ => @tmFail unit "lift_coinductive_relation: cannot locate prod or animation_result"
    end
  end.
Set Universe Checking.


(* ================================================================== *)
(** ** Transparent Sigma push: named holes with function types        *)
(* ================================================================== *)

(** Build the [mutual_inductive_body] for a fresh single-constructor wrapper
    inductive [Inductive wrapperName := mk_wrapperName : fn_type -> wrapperName].
    Used to generate named hole types for [TransparentSigmaPush].
    De Bruijn convention: inside [cstr_type] with 1 arg and 1 body block,
    the self-reference appears as [tRel 1] (depth 1 after the arg binder). *)
Definition make_wrapper_inductive_body
    (wrapper_name : ident)
    (fn_type      : term)
    : mutual_inductive_body :=
  let anon_b := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let ctor_body :=
    {| cstr_name    := "mk_" ++ wrapper_name;
       cstr_args    := [{| decl_name := anon_b; decl_body := None; decl_type := fn_type |}];
       cstr_indices := [];
       cstr_type    := tProd anon_b fn_type (tRel 1);
       cstr_arity   := 1 |} in
  let oib :=
    {| ind_name      := wrapper_name;
       ind_indices   := [];
       ind_sort      := Sort.type0;
       ind_type      := tSort Sort.type0;
       ind_kelim     := IntoAny;
       ind_ctors     := [ctor_body];
       ind_projs     := [];
       ind_relevance := Relevant |} in
  {| ind_finite    := Finite;
     ind_npars     := 0;
     ind_universes := Monomorphic_ctx;
     ind_variance  := None;
     ind_params    := [];
     ind_bodies    := [oib] |}.

(** Build the unwrap lambda for a named wrapper inductive.
    Returns [fun (w : W) => match w with mk_W f => f end : W -> fn_type].
    [wrapper_ind] is the inductive reference; [fn_type] is the wrapped type. *)
Definition build_unwrap_fn (wrapper_ind : inductive) (fn_type : term) : term :=
  let anon_b := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let w_type := tInd wrapper_ind [] in
  let ci     := {| ci_ind := wrapper_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let pred   := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := fn_type |} in
  let branch := {| bcontext := [anon_b]; bbody := tRel 0 |} in
  tLambda anon_b w_type (tCase ci pred (tRel 0) [branch]).

(** For each extra constructor in each lifted type, declare a wrapper inductive
    [Inductive ctorNameSymb := mk_ctorNameSymb : fnSymb_type -> ctorNameSymb] and a
    corresponding [ctorNameSymb_unwrap : ctorNameSymb -> fnSymb_type] definition.
    These are the named hole types for animation constructor positions in
    [TransparentSigmaPush]. *)
Polymorphic Fixpoint generate_fnSymb_wrapper_inductives
    (todo        : list (kername * inductive))
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (cur_mp      : modpath)
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
                   let fn_type := make_fnSymb_type new_ind n_bodies n_params c type_map app_kn_map in
                   fn_type_ev <- tmEval all fn_type ;;
                   let wrapper_nm := c.(cstr_name) ++ "Symb" in
                   let body := make_wrapper_inductive_body wrapper_nm fn_type_ev in
                   body_ev <- tmEval all body ;;
                   let W_ind := {| inductive_mind := (cur_mp, wrapper_nm); inductive_ind := 0 |} in
                   let unwrap_body := build_unwrap_fn W_ind fn_type_ev in
                   unwrap_ev <- tmEval all unwrap_body ;;
                   _ <- tmMkInductive' body_ev ;;
                   tmMkDefinition (wrapper_nm ++ "_unwrap") unwrap_ev))
                extra (tmReturn tt)
            end) (fun _ =>
    generate_fnSymb_wrapper_inductives rest type_map app_kn_map cur_mp)))
  end.

(** Return the first index i such that [f (nth i l)] is true, starting from
    [cur].  Returns [None] if no element satisfies [f]. *)
Fixpoint find_first_index_opt {A} (f : A -> bool) (l : list A) (cur : nat)
    : option nat :=
  match l with
  | []      => None
  | x :: xs => if f x then Some cur else find_first_index_opt f xs (S cur)
  end.

(** Deduplicate a list of hole-type terms by wrapper inductive identity
    ([inductive_mind] of the [tInd] node).  Returns [(unique_types, canon_map)]
    where [List.nth i canon_map 0] is the canonical index in [unique_types] for
    the i-th entry of the original list. *)
Fixpoint dedup_hole_types_go
    (todo      : list term)
    (seen      : list term)
    (seen_kns  : list kername)
    (canon_rev : list nat)
    : list term * list nat :=
  match todo with
  | []      => (seen, List.rev canon_rev)
  | t :: rest =>
    let opt_kn :=
      match t with
      | tInd ind _ => Some (inductive_mind ind)
      | _          => None
      end in
    match opt_kn with
    | None =>
      let j := List.length seen in
      dedup_hole_types_go rest (seen ++ [t]) seen_kns (j :: canon_rev)
    | Some kn =>
      match find_first_index_opt (eq_kername kn) seen_kns 0 with
      | Some j => dedup_hole_types_go rest seen seen_kns (j :: canon_rev)
      | None   =>
        let j := List.length seen in
        dedup_hole_types_go rest (seen ++ [t]) (seen_kns ++ [kn]) (j :: canon_rev)
      end
    end
  end.

Definition dedup_hole_types (types : list term) : list term * list nat :=
  dedup_hole_types_go types [] [] [].

(** Index of the first [tInd] entry in [unique_ht_terms] whose kername equals [kn].
    Returns 0 if not found. *)
Definition find_hole_idx_by_kn (kn : kername) (unique_ht_terms : list term) : nat :=
  match find_first_index_opt (fun ht =>
    match ht with tInd ind _ => eq_kername (inductive_mind ind) kn | _ => false end)
    unique_ht_terms 0 with
  | Some j => j
  | None   => 0
  end.

(** Compute the unique hole-type terms for [old_kn]'s transparent-sigma push body.
    Returns [(unique_ht_terms, canon_map)] ordered: coIndPushSymb (non-pi) first,
    then extra-ctor Symb holes, then transitively required holes from external types
    (looked up from [pi_set_holes]).  Duplicates collapsed by [dedup_hole_types]. *)
Definition compute_push_unique_holes
    (old_kn        : kername)
    (new_ind       : inductive)
    (n_block       : nat)
    (new_oib       : one_inductive_body)
    (n_old_ctors   : nat)
    (type_map      : list (kername * inductive))
    (pi_set        : list kername)
    (is_purely_ind : bool)
    (cur_mp        : modpath)
    (pi_set_holes  : list (kername * list term))
    : list term * list nat :=
  let new_kn   := inductive_mind new_ind in
  let body_idx := inductive_ind new_ind in
  let type_nm  := snd old_kn in
  let coind_ts :=
    if is_purely_ind then []
    else [tInd {| inductive_mind := (cur_mp, type_nm ++ "coIndPushSymb"); inductive_ind := 0 |} []] in
  let extra_ctor_ts :=
    List.flat_map (fun '(ctor_idx, ctor) =>
      if Nat.ltb ctor_idx n_old_ctors then []
      else [tInd {| inductive_mind := (cur_mp, ctor.(cstr_name) ++ "Symb"); inductive_ind := 0 |} []])
    (mapi (fun i c => (i, c)) new_oib.(ind_ctors)) in
  let external_ts :=
    List.flat_map (fun ctor =>
      let n_args := ctor.(cstr_arity) in
      List.flat_map (fun snoc_i =>
        let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                     | Some d => d.(decl_type) | None => tVar "?" end in
        match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
        | Some (Some kn) =>
          match find (fun e => eq_kername (fst e) kn) pi_set_holes with
          | Some (_, kn_hs) => kn_hs
          | None =>
            if existsb (eq_kername kn) pi_set then []
            else [tInd {| inductive_mind := (cur_mp, snd kn ++ "coIndPushSymb"); inductive_ind := 0 |} []]
          end
        | _ => []
        end)
      (seq 0 n_args))
    new_oib.(ind_ctors) in
  dedup_hole_types (coind_ts ++ extra_ctor_ts ++ external_ts).

(** Declare a wrapper inductive
    [Inductive typeNm{suffix} := mk_typeNm{suffix} : (T' -> T) -> typeNm{suffix}]
    and its unwrap function for each type in [todo].
    [for_pi = false]: generate for types NOT in [pi_set] (coIndPushSymb holes).
    [for_pi = true]:  generate for types IN [pi_set]     (PushFullSymb holes). *)
Polymorphic Fixpoint generate_pushSymb_wrapper_inductives
    (todo        : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map     : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (pi_set      : list kername)
    (cur_mp      : modpath)
    (suffix      : string)
    (for_pi      : bool)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), _) :: rest =>
    tmBind (if Bool.eqb for_pi (existsb (eq_kername old_kn) pi_set) then
              let old_type := subst_ind_to_old all_map app_kn_map new_ind in
              let new_type := tInd new_ind [] in
              let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
              let push_fn_type := tProd anon_b new_type old_type in
              push_fn_type_ev <- tmEval all push_fn_type ;;
              let wrapper_nm := snd old_kn ++ suffix in
              let body := make_wrapper_inductive_body wrapper_nm push_fn_type_ev in
              body_ev <- tmEval all body ;;
              let W_ind := {| inductive_mind := (cur_mp, wrapper_nm); inductive_ind := 0 |} in
              let unwrap_body := build_unwrap_fn W_ind push_fn_type_ev in
              unwrap_ev <- tmEval all unwrap_body ;;
              _ <- tmMkInductive' body_ev ;;
              tmMkDefinition (wrapper_nm ++ "_unwrap") unwrap_ev
            else tmReturn tt)
    (fun _ => generate_pushSymb_wrapper_inductives rest all_map app_kn_map pi_set cur_mp suffix for_pi)
  end.

(** Build the [def term] for the transparent-sigma push function of [old_kn].
    Returns [HoleyResult old_type] with named wrapper hole types:
    - Regular constructors: same hr_ap fold as [make_push_def].
    - Animation / extra constructors: named fn wrapper hole (ctorNameSymb) applied
      to pushed original-type args (PlainPush for pi, coIndPushSymb hole for npi).
    - Depth-0 branch (non-pi only): named coIndPushSymb hole applied to scrutinee. *)
Definition make_transparent_sigma_push_def
    (old_kn        : kername)
    (new_ind       : inductive)
    (n_block       : nat)
    (new_oib       : one_inductive_body)
    (n_old_ctors   : nat)
    (type_map      : list (kername * inductive))
    (app_kn_map    : list (kername * list term * inductive))
    (pi_set        : list kername)
    (is_purely_ind : bool)
    (cur_mp        : modpath)
    (hr_hole_c     : term)
    (hr_pure_c     : term)
    (hr_ap_c       : term)
    (hr_map_c      : term)
    (hr_type_c     : term)
    : def term :=
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
    | None                => []
    | Some (_, arg_terms) => arg_terms
    end in
  let old_type :=
    match par_terms with
    | [] => tInd head_ind []
    | _  => tApp (tInd head_ind []) par_terms
    end in
  let holey_old_type := tApp hr_type_c [old_type] in
  let new_type     := tInd new_ind [] in
  let type_nm      := snd old_kn in
  let new_kn       := inductive_mind new_ind in
  let body_idx     := inductive_ind new_ind in
  let anon_b       := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let self_coind_symb_ind :=
    {| inductive_mind := (cur_mp, type_nm ++ "coIndPushSymb"); inductive_ind := 0 |} in
  let self_coind_symb_type := tInd self_coind_symb_ind [] in
  (* Number of parameters for make_fnSymb_type. *)
  let n_params :=
    match nth_error new_oib.(ind_ctors) 0 with
    | None   => 0
    | Some _ =>
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 app_kn_map with
      | Some e => List.length (snd (fst e))
      | None   => 0
      end
    end in
  let branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      let bbody :=
        if Nat.ltb ctor_idx n_old_ctors then
          (* Regular constructor: fold hr_ap over pushed args (same as make_push_def). *)
          let push_and_types_snoc :=
            List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
              | Some None =>
                  let self_push :=
                    if is_purely_ind then
                      tApp (tRel (n_args + 1)) [tRel snoc_i]
                    else
                      tApp (tRel (n_args + 3)) [tRel n_args; tRel snoc_i] in
                  (self_push, old_type)
              | Some (Some kn) =>
                  let push_const := tConst (cur_mp, snd kn ++ "TransparentSigmaPush") [] in
                  let ext_push :=
                    if existsb (eq_kername kn) pi_set then
                      tApp push_const [tRel snoc_i]
                    else
                      tApp push_const [tRel n_args; tRel snoc_i] in
                  let kn_ind := {| inductive_mind := kn; inductive_ind := 0 |} in
                  let lifted_for_kn :=
                    match find (fun e => eq_kername (fst e) kn) type_map with
                    | Some (_, ni) => ni
                    | None         => kn_ind
                    end in
                  let orig_arg_t :=
                    match find (fun e =>
                                  andb (eq_kername (inductive_mind (snd e))
                                                   (inductive_mind lifted_for_kn))
                                       (Nat.eqb (inductive_ind (snd e))
                                                (inductive_ind lifted_for_kn)))
                               app_kn_map with
                    | Some ((head_kn, params), _) =>
                        match params with
                        | [] => tInd {| inductive_mind := head_kn; inductive_ind := 0 |} []
                        | _  => tApp (tInd {| inductive_mind := head_kn; inductive_ind := 0 |} []) params
                        end
                    | None => tInd kn_ind []
                    end in
                  (ext_push, orig_arg_t)
              | None =>
                  (tApp hr_pure_c [arg_t; tRel snoc_i], arg_t)
              end)
            (seq 0 n_args) in
          let push_and_types := List.rev push_and_types_snoc in
          let holey_args     := List.map fst push_and_types in
          let orig_arg_types := List.map snd push_and_types in
          let B_types :=
            List.fold_right (fun orig_t acc =>
              tProd anon_b orig_t (List.hd old_type acc) :: acc)
            [old_type] orig_arg_types in
          let base_ctor :=
            match par_terms with
            | [] => tConstruct head_ind ctor_idx []
            | _  => tApp (tConstruct head_ind ctor_idx []) par_terms
            end in
          let full_ctor_type := List.hd old_type B_types in
          let init_holey := tApp hr_pure_c [full_ctor_type; base_ctor] in
          fst (List.fold_left
            (fun '(current, b_list) '(holey_arg, orig_t) =>
              match b_list with
              | _ :: b_rest =>
                  let b_next := List.hd old_type b_rest in
                  (tApp hr_ap_c [orig_t; b_next; current; holey_arg], b_rest)
              | [] => (current, [])
              end)
            (List.combine holey_args orig_arg_types)
            (init_holey, B_types))
        else
          (* Animation/extra constructor: named fn-wrapper hole applied to original-type args. *)
          let fn_type := make_fnSymb_type new_ind n_block n_params ctor type_map app_kn_map in
          let W_ind   := {| inductive_mind := (cur_mp, ctor.(cstr_name) ++ "Symb"); inductive_ind := 0 |} in
          let W_type  := tInd W_ind [] in
          let unwrap  := tConst (cur_mp, ctor.(cstr_name) ++ "Symb_unwrap") [] in
          let init_holey :=
            tApp hr_map_c [W_type; fn_type; unwrap; tApp hr_hole_c [W_type]] in
          let push_and_types_snoc :=
            List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
              | Some None =>
                  if is_purely_ind then
                    (tApp (tRel (n_args + 1)) [tRel snoc_i], old_type)
                  else
                    let coind_push_fn_t := tProd anon_b new_type old_type in
                    let coind_unwrap := tConst (cur_mp, type_nm ++ "coIndPushSymb_unwrap") [] in
                    let coind_hole := tApp hr_map_c [
                        self_coind_symb_type; coind_push_fn_t; coind_unwrap;
                        tApp hr_hole_c [self_coind_symb_type]] in
                    let holey_arg := tApp hr_ap_c [
                        new_type; old_type; coind_hole;
                        tApp hr_pure_c [new_type; tRel snoc_i]] in
                    (holey_arg, old_type)
              | Some (Some kn) =>
                  let is_kn_pi := existsb (eq_kername kn) pi_set in
                  let kn_ind := {| inductive_mind := kn; inductive_ind := 0 |} in
                  let lifted_for_kn :=
                    match find (fun e => eq_kername (fst e) kn) type_map with
                    | Some (_, ni) => ni | None => kn_ind end in
                  let orig_kn_t :=
                    match find (fun e =>
                                  andb (eq_kername (inductive_mind (snd e))
                                                   (inductive_mind lifted_for_kn))
                                       (Nat.eqb (inductive_ind (snd e))
                                                (inductive_ind lifted_for_kn)))
                               app_kn_map with
                    | Some ((head_kn, params), _) =>
                        match params with
                        | [] => tInd {| inductive_mind := head_kn; inductive_ind := 0 |} []
                        | _  => tApp (tInd {| inductive_mind := head_kn; inductive_ind := 0 |} []) params
                        end
                    | None => tInd kn_ind []
                    end in
                  let kn_new_type := tInd lifted_for_kn [] in
                  if is_kn_pi then
                    let push_const := tConst (cur_mp, snd kn ++ "TransparentSigmaPush") [] in
                    (tApp push_const [tRel snoc_i], orig_kn_t)
                  else
                    let kn_coind_symb_ind :=
                      {| inductive_mind := (cur_mp, snd kn ++ "coIndPushSymb"); inductive_ind := 0 |} in
                    let kn_coind_symb_type := tInd kn_coind_symb_ind [] in
                    let kn_coind_push_fn_t := tProd anon_b kn_new_type orig_kn_t in
                    let kn_coind_unwrap := tConst (cur_mp, snd kn ++ "coIndPushSymb_unwrap") [] in
                    let kn_coind_hole := tApp hr_map_c [
                        kn_coind_symb_type; kn_coind_push_fn_t; kn_coind_unwrap;
                        tApp hr_hole_c [kn_coind_symb_type]] in
                    let holey_arg := tApp hr_ap_c [
                        kn_new_type; orig_kn_t; kn_coind_hole;
                        tApp hr_pure_c [kn_new_type; tRel snoc_i]] in
                    (holey_arg, orig_kn_t)
              | None =>
                  (tApp hr_pure_c [arg_t; tRel snoc_i], arg_t)
              end)
            (seq 0 n_args) in
          let push_and_types := List.rev push_and_types_snoc in
          let holey_args     := List.map fst push_and_types in
          let orig_arg_types := List.map snd push_and_types in
          let B_types :=
            List.fold_right (fun orig_t acc =>
              tProd anon_b orig_t (List.hd old_type acc) :: acc)
            [old_type] orig_arg_types in
          fst (List.fold_left
            (fun '(current, b_list) '(holey_arg, orig_t) =>
              match b_list with
              | _ :: b_rest =>
                  let b_next := List.hd old_type b_rest in
                  (tApp hr_ap_c [orig_t; b_next; current; holey_arg], b_rest)
              | [] => (current, [])
              end)
            (List.combine holey_args orig_arg_types)
            (init_holey, B_types))
      in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    new_oib.(ind_ctors) in
  let pred  := {| puinst := []; pparams := [];
                  pcontext := [anon_b];
                  preturn  := holey_old_type |} in
  let ci    := {| ci_ind := new_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let dname := {| binder_name := nNamed (type_nm ++ "TransparentSigmaPush");
                  binder_relevance := Relevant |} in
  if is_purely_ind then
    {| dname := dname;
       dtype  := tProd anon_b new_type holey_old_type;
       dbody  := tLambda anon_b new_type (tCase ci pred (tRel 0) branches);
       rarg   := 0 |}
  else
    let nat_ind_ref := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
    let nat_ci   := {| ci_ind := nat_ind_ref; ci_npar := 0; ci_relevance := Relevant |} in
    let nat_pred := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := holey_old_type |} in
    let inner_case := tCase ci pred (tRel 1) branches in
    (* Depth-0: coIndPushSymb hole applied to scrutinee (tRel 0 inside the 0-branch). *)
    let coind_push_fn_t := tProd anon_b new_type old_type in
    let coind_unwrap    := tConst (cur_mp, type_nm ++ "coIndPushSymb_unwrap") [] in
    let coind_hole      := tApp hr_map_c [
        self_coind_symb_type; coind_push_fn_t; coind_unwrap;
        tApp hr_hole_c [self_coind_symb_type]] in
    let o_branch_body   := tApp hr_ap_c [
        new_type; old_type; coind_hole; tApp hr_pure_c [new_type; tRel 0]] in
    let o_branch   := {| bcontext := []; bbody := o_branch_body |} in
    let s_branch   := {| bcontext := [anon_b]; bbody := inner_case |} in
    let dbody :=
      tLambda anon_b (tInd nat_ind_ref [])
        (tLambda anon_b new_type
          (tCase nat_ci nat_pred (tRel 1) [o_branch; s_branch])) in
    {| dname := dname;
       dtype  := tProd anon_b (tInd nat_ind_ref []) (tProd anon_b new_type holey_old_type);
       dbody  := dbody;
       rarg   := 0 |}.

(** Build the body fixpoint [def term] for [typeNmTransparentSigmaPushBody].
    The body takes hole values as leading parameters, then depth (non-pi only), then
    the new-type scrutinee, and returns [old_type] directly (no HoleyResult).
    Self-recursive and external-type calls pass hole values through explicitly so that
    the resulting wrapper can use a STATIC hole list with no duplicates. *)
Definition make_transparent_sigma_push_body_def
    (old_kn          : kername)
    (new_ind         : inductive)
    (n_block         : nat)
    (new_oib         : one_inductive_body)
    (n_old_ctors     : nat)
    (type_map        : list (kername * inductive))
    (app_kn_map      : list (kername * list term * inductive))
    (pi_set          : list kername)
    (is_purely_ind   : bool)
    (cur_mp          : modpath)
    (unique_ht_terms : list term)
    (pi_set_holes    : list (kername * list term))
    : def term :=
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
    | None                => []
    | Some (_, arg_terms) => arg_terms
    end in
  let old_type :=
    match par_terms with
    | [] => tInd head_ind []
    | _  => tApp (tInd head_ind []) par_terms
    end in
  let new_type   := tInd new_ind [] in
  let type_nm    := snd old_kn in
  let new_kn     := inductive_mind new_ind in
  let body_idx   := inductive_ind new_ind in
  let anon_b     := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let n_holes    := List.length unique_ht_terms in
  (* De-Bruijn ref to hole k (0 = outermost) inside a S-branch ctor body. *)
  let s_hole_ref := fun (n_args k : nat) =>
    if is_purely_ind then tRel (n_args + n_holes - k)
    else tRel (n_args + 2 + n_holes - k) in
  (* All hole refs [h_0; ...; h_{n-1}] inside S-branch ctor body. *)
  let all_s_hole_refs := fun (n_args : nat) =>
    List.map (fun k => s_hole_ref n_args k) (seq 0 n_holes) in
  (* Fix self-ref inside S-branch ctor body. *)
  let s_fix_ref := fun (n_args : nat) =>
    if is_purely_ind then tRel (n_args + n_holes + 1)
    else tRel (n_args + n_holes + 3) in
  (* Hole refs for kn's unique holes remapped to current type's positions. *)
  let kn_hole_refs_in_s := fun (n_args : nat) (kn : kername) =>
    let kn_hs := match find (fun e => eq_kername (fst e) kn) pi_set_holes with
                 | Some (_, hs) => hs | None => [] end in
    List.map (fun h_t =>
      match h_t with
      | tInd ind _ => s_hole_ref n_args (find_hole_idx_by_kn (inductive_mind ind) unique_ht_terms)
      | _          => tVar "hole_kn_not_found"
      end)
    kn_hs in
  let branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      let bbody :=
        if Nat.ltb ctor_idx n_old_ctors then
          (* Regular constructor: apply ctor to pushed args. *)
          let pushed_snoc :=
            List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
              | Some None =>
                let call_args :=
                  List.app (all_s_hole_refs n_args)
                  (List.app (if is_purely_ind then [] else [tRel n_args])
                             [tRel snoc_i]) in
                tApp (s_fix_ref n_args) call_args
              | Some (Some kn) =>
                let body_c := tConst (cur_mp, snd kn ++ "TransparentSigmaPushBody") [] in
                let kn_h_list : list term := kn_hole_refs_in_s n_args kn in
                let call_args :=
                  List.app kn_h_list
                  (List.app (if existsb (eq_kername kn) pi_set then [] else [tRel n_args])
                             [tRel snoc_i]) in
                tApp body_c call_args
              | None => tRel snoc_i
              end)
            (seq 0 n_args) in
          let pushed    := List.rev pushed_snoc in
          let ctor_base := match par_terms with
            | [] => tConstruct head_ind ctor_idx []
            | _  => tApp (tConstruct head_ind ctor_idx []) par_terms end in
          match pushed with
          | [] => ctor_base
          | _  => tApp ctor_base pushed
          end
        else
          (* Animation/extra constructor: apply Symb_unwrap hole to pushed args. *)
          let ctor_nm  := ctor.(cstr_name) in
          let w_kn     := (cur_mp, ctor_nm ++ "Symb") in
          let w_idx    := find_hole_idx_by_kn w_kn unique_ht_terms in
          let fn_ref   := tApp (tConst (cur_mp, ctor_nm ++ "Symb_unwrap") [])
                               [s_hole_ref n_args w_idx] in
          let pushed_snoc :=
            List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
              | Some None =>
                if is_purely_ind then
                  tApp (s_fix_ref n_args) (List.app (all_s_hole_refs n_args) [tRel snoc_i])
                else
                  let coind_kn  := (cur_mp, type_nm ++ "coIndPushSymb") in
                  let coind_idx := find_hole_idx_by_kn coind_kn unique_ht_terms in
                  tApp (tConst (cur_mp, type_nm ++ "coIndPushSymb_unwrap") [])
                       [s_hole_ref n_args coind_idx; tRel snoc_i]
              | Some (Some kn) =>
                let kn_h_refs : list term := kn_hole_refs_in_s n_args kn in
                if existsb (eq_kername kn) pi_set then
                  tApp (tConst (cur_mp, snd kn ++ "TransparentSigmaPushBody") [])
                       (List.app kn_h_refs [tRel snoc_i])
                else
                  let kn_coind_kn  := (cur_mp, snd kn ++ "coIndPushSymb") in
                  let kn_coind_idx := find_hole_idx_by_kn kn_coind_kn unique_ht_terms in
                  tApp (tConst (cur_mp, snd kn ++ "coIndPushSymb_unwrap") [])
                       [s_hole_ref n_args kn_coind_idx; tRel snoc_i]
              | None => tRel snoc_i
              end)
            (seq 0 n_args) in
          let pushed := List.rev pushed_snoc in
          match pushed with
          | [] => fn_ref
          | _  => tApp fn_ref pushed
          end
      in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    new_oib.(ind_ctors) in
  let pred  := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := old_type |} in
  let ci    := {| ci_ind := new_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let dname := {| binder_name := nNamed (type_nm ++ "TransparentSigmaPushBody");
                  binder_relevance := Relevant |} in
  let base_dtype :=
    if is_purely_ind then tProd anon_b new_type old_type
    else let nat_r := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
         tProd anon_b (tInd nat_r []) (tProd anon_b new_type old_type) in
  let dtype := List.fold_right (fun h_t acc => tProd anon_b h_t acc) base_dtype unique_ht_terms in
  if is_purely_ind then
    let dbody :=
      List.fold_right (fun h_t acc => tLambda anon_b h_t acc)
        (tLambda anon_b new_type (tCase ci pred (tRel 0) branches))
        unique_ht_terms in
    {| dname := dname; dtype := dtype; dbody := dbody; rarg := n_holes |}
  else
    let nat_ind_ref := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
    let nat_ci   := {| ci_ind := nat_ind_ref; ci_npar := 0; ci_relevance := Relevant |} in
    let nat_pred := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := old_type |} in
    let inner_case := tCase ci pred (tRel 1) branches in
    (* O-branch: coIndPushSymb_unwrap h_coind s.
       In o-branch context (no ctor args, no S-binder): tRel 0 = s, tRel 1 = depth,
       tRel 2 = h_{n-1}, ..., tRel 1+n_holes = h_0, tRel 2+n_holes = f. *)
    let coind_kn      := (cur_mp, type_nm ++ "coIndPushSymb") in
    let coind_idx     := find_hole_idx_by_kn coind_kn unique_ht_terms in
    let o_coind_ref   := tRel (1 + n_holes - coind_idx) in
    let o_branch_body := tApp (tConst (cur_mp, type_nm ++ "coIndPushSymb_unwrap") [])
                              [o_coind_ref; tRel 0] in
    let o_branch := {| bcontext := []; bbody := o_branch_body |} in
    let s_branch := {| bcontext := [anon_b]; bbody := inner_case |} in
    let dbody :=
      List.fold_right (fun h_t acc => tLambda anon_b h_t acc)
        (tLambda anon_b (tInd nat_ind_ref [])
          (tLambda anon_b new_type
            (tCase nat_ci nat_pred (tRel 1) [o_branch; s_branch])))
        unique_ht_terms in
    {| dname := dname; dtype := dtype; dbody := dbody; rarg := n_holes |}.

(** Build the wrapper term for [typeNmTransparentSigmaPush] that wraps the body
    in a HoleyResult with exactly [unique_ht_terms] as the static hole list. *)
Definition make_transparent_sigma_push_wrapper_term
    (old_kn          : kername)
    (new_ind         : inductive)
    (type_map        : list (kername * inductive))
    (app_kn_map      : list (kername * list term * inductive))
    (is_purely_ind   : bool)
    (cur_mp          : modpath)
    (unique_ht_terms : list term)
    (hr_pure_c hr_ap_c hr_hole_c : term)
    : term :=
  let old_type    := subst_ind_to_old type_map app_kn_map new_ind in
  let new_type    := tInd new_ind [] in
  let anon_b      := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let nat_ind_ref := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
  let body_c      := tConst (cur_mp, snd old_kn ++ "TransparentSigmaPushBody") [] in
  let n_holes     := List.length unique_ht_terms in
  (* Inside n_holes inner lambdas: tRel 0 = h_{n-1}, ..., tRel n_holes-1 = h_0.
     Outer lambdas: non-pi -> tRel n_holes = s, tRel n_holes+1 = depth;
                    pi     -> tRel n_holes = s. *)
  let hole_args :=
    List.map (fun k => tRel (n_holes - 1 - k)) (seq 0 n_holes) in
  let s_ref    := tRel n_holes in
  let body_call :=
    if is_purely_ind then tApp body_c (hole_args ++ [s_ref])
    else tApp body_c (hole_args ++ [tRel (n_holes + 1); s_ref]) in
  (* inner_fn: tLambda H_0 (... (tLambda H_{n-1} body_call) ...) *)
  let inner_fn :=
    List.fold_right (fun h_t acc => tLambda anon_b h_t acc) body_call unique_ht_terms in
  (* B-type chain: [B_0; B_1; ...; B_{n-1}; old_type]
     where B_k = H_k -> B_{k+1}. *)
  let b_type_chain :=
    List.fold_right (fun h_t acc => tProd anon_b h_t (List.hd old_type acc) :: acc)
      [old_type] unique_ht_terms in
  (* Build the hr_ap chain: step by step applying hr_hole for each hole type. *)
  let init_hr := tApp hr_pure_c [List.hd old_type b_type_chain; inner_fn] in
  let '(_, final_hr) :=
    List.fold_left
      (fun '(b_tail, cur_hr) h_t =>
        let b_cur := List.hd old_type b_tail in
        (List.tl b_tail, tApp hr_ap_c [h_t; b_cur; cur_hr; tApp hr_hole_c [h_t]]))
      unique_ht_terms
      (List.tl b_type_chain, init_hr) in
  if is_purely_ind then tLambda anon_b new_type final_hr
  else tLambda anon_b (tInd nat_ind_ref []) (tLambda anon_b new_type final_hr).

(** Declare [typeNmTransparentSigmaPushBody] and [typeNmTransparentSigmaPush]
    for every type in [todo].  Pi-set types must appear before non-pi types in
    [todo] so that body constants are declared before they are referenced. *)
Polymorphic Fixpoint generate_transparent_sigma_push_fns
    (todo           : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map        : list (kername * inductive))
    (app_kn_map     : list (kername * list term * inductive))
    (pi_set         : list kername)
    (cur_mp         : modpath)
    (hr_hole_c      : term)
    (hr_pure_c      : term)
    (hr_ap_c        : term)
    (hr_map_c       : term)
    (hr_type_c      : term)
    (pi_set_holes   : list (kername * list term))
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
    let n_old_ctors :=
      match nth_error old_mind.(ind_bodies) 0 with
      | Some ob => List.length ob.(ind_ctors) | None => 0
      end in
    let n_block       := List.length new_mind.(ind_bodies) in
    let is_purely_ind := existsb (eq_kername old_kn) pi_set in
    let '(unique_ht_terms, _) :=
      match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
      | Some new_oib =>
        compute_push_unique_holes old_kn new_ind n_block new_oib n_old_ctors
          all_map pi_set is_purely_ind cur_mp pi_set_holes
      | None => ([], [])
      end in
    tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
            | None =>
              tmFail ("generate_transparent_sigma_push_fns: no body for " ++ snd old_kn)
            | Some new_oib =>
              let d_body := make_transparent_sigma_push_body_def
                              old_kn new_ind n_block new_oib n_old_ctors
                              all_map app_kn_map pi_set is_purely_ind cur_mp
                              unique_ht_terms pi_set_holes in
              body_ev <- tmEval all (tFix [d_body] 0) ;;
              _ <- tmMkDefinition (snd old_kn ++ "TransparentSigmaPushBody") body_ev ;;
              wrapper_ev <- tmEval all (make_transparent_sigma_push_wrapper_term
                              old_kn new_ind all_map app_kn_map is_purely_ind cur_mp
                              unique_ht_terms hr_pure_c hr_ap_c hr_hole_c) ;;
              tmMkDefinition (snd old_kn ++ "TransparentSigmaPush") wrapper_ev
            end)
    (fun _ =>
      generate_transparent_sigma_push_fns rest all_map app_kn_map pi_set cur_mp
        hr_hole_c hr_pure_c hr_ap_c hr_map_c hr_type_c
        (pi_set_holes ++ [(old_kn, unique_ht_terms)]))
  end.

(** Classify an output type for the transparent-sigma output push:
    uses [typeNmTransparentSigmaPush] (returns [HoleyResult T] with named holes). *)
Definition classify_out_type_transparent_sigma
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (pi_set     : list kername)
    (cur_mp     : modpath)
    (t          : term)
    : term * option (term * bool) :=
  match t with
  | tInd ind _ =>
    let kn := inductive_mind ind in
    match find (fun e => eq_kername (fst e) kn) type_map with
    | Some (old_kn, new_ind) =>
      let is_pi := existsb (eq_kername old_kn) pi_set in
      (tInd new_ind [],
       Some (tConst (cur_mp, snd old_kn ++ "TransparentSigmaPush") [], is_pi))
    | None => (t, None)
    end
  | tApp (tInd ind _) args =>
    let kn := inductive_mind ind in
    let found :=
      if negb (forallb is_ind_type args) then None
      else
        find (fun e =>
                andb (eq_kername (fst (fst e)) kn)
                     (andb (Nat.eqb #|snd (fst e)| #|args|)
                           (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                                    (combine (snd (fst e)) args))))
             app_kn_map in
    match found with
    | Some (_, new_ind) =>
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 type_map with
      | Some (old_kn, _) =>
        let is_pi := existsb (eq_kername old_kn) pi_set in
        (tInd new_ind [],
         Some (tConst (cur_mp, snd old_kn ++ "TransparentSigmaPush") [], is_pi))
      | None => (t, None)
      end
    | None => (t, None)
    end
  | _ => (t, None)
  end.

(** Declare [relTransparentSigmaOutputPush] for every entry in [kn_mode_list]. *)
Polymorphic Fixpoint generate_transparent_sigma_outputPush_fns
    (todo        : list (inductive * (string * (list nat * list nat))))
    (type_map    : list (kername * inductive))
    (app_kn_map  : list (kername * list term * inductive))
    (pi_set      : list kername)
    (prod_kn     : kername)
    (anim_res_kn : kername)
    (cur_mp      : modpath)
    (hr_type_c   : term)
    (hr_pair_c   : term)
    (hr_pure_c   : term)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let block_kn := inductive_mind (fst entry) in
    let rel_name := fst (snd entry) in
    let in_pos   := fst (snd (snd entry)) in
    let out_pos  := snd (snd (snd entry)) in
    tmBind (tmQuoteInductive block_kn) (fun orig_mind =>
    match find (fun ob => String.eqb ob.(ind_name) rel_name) orig_mind.(ind_bodies) with
    | None =>
      tmFail ("generate_transparent_sigma_outputPush_fns: cannot find body " ++ rel_name)
    | Some oib =>
      let n_params   := orig_mind.(ind_npars) in
      let n_total    := List.length in_pos + List.length out_pos in
      let all_types  := extract_arg_types n_params n_total oib.(ind_type) in
      let orig_types := List.map (fun p => nth p all_types (tVar "?")) out_pos in
      let classified   :=
        List.map (classify_out_type_transparent_sigma type_map app_kn_map pi_set cur_mp)
                 orig_types in
      let lifted_types := List.map fst classified in
      let push_fns     := List.map snd classified in
      let fn_term := make_outputPush_term prod_kn anim_res_kn orig_types lifted_types push_fns
                                          hr_type_c hr_pair_c hr_pure_c in
      fn_term_ev <- tmEval all fn_term ;;
      tmBind (tmMkDefinition (rel_name ++ "TransparentSigmaOutputPush") fn_term_ev) (fun _ =>
      generate_transparent_sigma_outputPush_fns rest type_map app_kn_map pi_set
                               prod_kn anim_res_kn cur_mp hr_type_c hr_pair_c hr_pure_c)
    end)
  end.


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
Definition animate_coinductive_opaque_sigma
    (rel_kn : kername)
    (modes  : mode_map)
    (fuel   : nat)
    : TemplateMonad unit :=
  let rel_nm := snd rel_kn in
  lift_coinductive_relation modes fuel ;;
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
      tmFail "animate_coinductive_opaque_sigma: cannot locate prod or animation_result"
    end
  | None, _ => tmFail ("animate_coinductive_opaque_sigma: no mode entry for " ++ rel_nm)
  | _, None  => tmFail ("animate_coinductive_opaque_sigma: cannot find body " ++ rel_nm)
  end.

(* ================================================================== *)
(** ** Transparent sigma property generation                           *)
(* ================================================================== *)

(** Extract binders from a product type in declaration order (outermost first). *)
Fixpoint extract_prod_args (t : term) : list (aname * term) * term :=
  match t with
  | tProd nm T body =>
    let '(rest, ret) := extract_prod_args body in
    ((nm, T) :: rest, ret)
  | _ => ([], t)
  end.

(** Substitute block-body references encoded as [tRel] with concrete [tInd] refs.
    At depth [d], body j is encoded as [tRel (d + n_bodies - 1 - j)]. *)
Fixpoint subst_new_block_at_depth
    (new_kn   : kername)
    (n_bodies : nat)
    (depth    : nat)
    (t        : term)
    : term :=
  match t with
  | tRel k =>
    if andb (Nat.leb depth k) (Nat.ltb k (depth + n_bodies)) then
      let j := depth + n_bodies - 1 - k in
      tInd {| inductive_mind := new_kn; inductive_ind := j |} []
    else tRel k
  | tApp f args =>
    tApp (subst_new_block_at_depth new_kn n_bodies depth f)
         (List.map (subst_new_block_at_depth new_kn n_bodies depth) args)
  | tProd nm ty body =>
    tProd nm (subst_new_block_at_depth new_kn n_bodies depth ty)
             (subst_new_block_at_depth new_kn n_bodies (S depth) body)
  | _ => t
  end.

(** Build [forall a1..an, old_rel a1..an (fn_tm_lifted a1..an)].
    [fn_tm] is the unwrapped hole function at depth 0 (outside the arg foralls);
    it is lifted by [n_args] before use so outer hole tRels survive the binders.
    [fnSymb_ty] = result of [make_fnSymb_type] (product of original-type arg types). *)
Definition build_an_hole_prop
    (old_ind   : inductive)
    (new_ind   : inductive)
    (fn_tm     : term)
    (fnSymb_ty : term)
    : term :=
  let old_rel_ind := old_ind in
  let '(arg_pairs, _) := extract_prod_args fnSymb_ty in
  let n_args    := List.length arg_pairs in
  let fn_tm_in  := lift n_args 0 fn_tm in
  let rel_args  := mapi (fun i _ => tRel (n_args - 1 - i)) arg_pairs in
  let fnSymb_app :=
    match arg_pairs with
    | [] => fn_tm_in
    | _  => tApp fn_tm_in rel_args
    end in
  let rel_app := tApp (tInd old_rel_ind []) (rel_args ++ [fnSymb_app]) in
  List.fold_right (fun '(nm, T) acc => tProd nm T acc) rel_app arg_pairs.

(** Build [forall new_ctor_args, (push_tm_lifted) (new_ctor ...) = old_ctor ((sub_push_tm_lifted) ...)].
    [push_tm] is the unwrapped push-hole function at depth 0; it is lifted by [n_args]
    before use so the outer hole tRel survives the inner binders.
    [push_hole_map] maps each old coinductive kname to its push-hole term at depth 0,
    used to apply the correct hole to recursive sub-arguments.
    Uses [subst_new_block_at_depth] to fix up block-relative tRels in arg types.
    [eq_ind_tm] = the [tInd eq_ind ui] term for [@eq]; [old_type] = original type. *)
Definition build_coIndPush_eq_for_ctor
    (old_kn        : kername)
    (new_ind       : inductive)
    (new_kn        : kername)
    (n_bodies      : nat)
    (ctor_idx      : nat)
    (new_ctor      : constructor_body)
    (type_map      : list (kername * inductive))
    (pi_set        : list kername)
    (push_tm       : term)
    (push_hole_map : list (kername * term))
    (pi_push_map   : list (kername * term))
    (eq_ind_tm     : term)
    (old_type      : term)
    : term :=
  let old_ind    := {| inductive_mind := old_kn; inductive_ind := inductive_ind new_ind |} in
  let n_args     := new_ctor.(cstr_arity) in
  let push_fn_in := lift n_args 0 push_tm in
  let arg_types_decl :=
    mapi (fun i d =>
      (d.(decl_name), subst_new_block_at_depth new_kn n_bodies i d.(decl_type)))
    (List.rev new_ctor.(cstr_args)) in
  let arg_rels := mapi (fun i _ => tRel (n_args - 1 - i)) arg_types_decl in
  let new_ctor_app :=
    match arg_rels with
    | [] => tConstruct new_ind ctor_idx []
    | _  => tApp (tConstruct new_ind ctor_idx []) arg_rels
    end in
  let lhs := tApp push_fn_in [new_ctor_app] in
  let pushed_args :=
    mapi (fun i '(_, ty) =>
      let arg_rel := tRel (n_args - 1 - i) in
      match ind_of_type ty with
      | None => arg_rel
      | Some ind =>
        match find (fun e =>
                      andb (eq_kername (inductive_mind (snd e)) (inductive_mind ind))
                           (Nat.eqb (inductive_ind (snd e)) (inductive_ind ind)))
                   type_map with
        | Some (kn, _) =>
          if existsb (eq_kername kn) pi_set then
            match find (fun e => eq_kername (fst e) kn) pi_push_map with
            | Some (_, pi_push_fn) => tApp (lift n_args 0 pi_push_fn) [arg_rel]
            | None => arg_rel
            end
          else
            match find (fun e => eq_kername (fst e) kn) push_hole_map with
            | Some (_, sub_push_tm) => tApp (lift n_args 0 sub_push_tm) [arg_rel]
            | None => arg_rel
            end
        | None => arg_rel
        end
      end)
    arg_types_decl in
  let old_ctor_app :=
    match pushed_args with
    | [] => tConstruct old_ind ctor_idx []
    | _  => tApp (tConstruct old_ind ctor_idx []) pushed_args
    end in
  let eq_body := tApp eq_ind_tm [old_type; lhs; old_ctor_app] in
  List.fold_right (fun '(nm, T) acc => tProd nm T acc) eq_body arg_types_decl.

(** Build [forall new_ctor_args, (push_tm_lifted) (extra_ctor ...) = (fn_tm_lifted) ((sub_push_tm_lifted) ...)].
    Like [build_coIndPush_eq_for_ctor] but the RHS uses [fn_tm] (the unwrapped An-hole
    function for this extra constructor) rather than an original constructor.
    Both [push_tm] and [fn_tm] are at depth 0 and are lifted by [n_args] inside. *)
Definition build_coIndPush_eq_for_extra_ctor
    (old_kn        : kername)
    (new_ind       : inductive)
    (new_kn        : kername)
    (n_bodies      : nat)
    (ctor_idx      : nat)
    (new_ctor      : constructor_body)
    (type_map      : list (kername * inductive))
    (pi_set        : list kername)
    (push_tm       : term)
    (push_hole_map : list (kername * term))
    (pi_push_map   : list (kername * term))
    (fn_tm         : term)
    (eq_ind_tm     : term)
    (old_type      : term)
    : term :=
  let n_args     := new_ctor.(cstr_arity) in
  let push_fn_in := lift n_args 0 push_tm in
  let fn_in      := lift n_args 0 fn_tm in
  let arg_types_decl :=
    mapi (fun i d =>
      (d.(decl_name), subst_new_block_at_depth new_kn n_bodies i d.(decl_type)))
    (List.rev new_ctor.(cstr_args)) in
  let arg_rels := mapi (fun i _ => tRel (n_args - 1 - i)) arg_types_decl in
  let new_ctor_app :=
    match arg_rels with
    | [] => tConstruct new_ind ctor_idx []
    | _  => tApp (tConstruct new_ind ctor_idx []) arg_rels
    end in
  let lhs := tApp push_fn_in [new_ctor_app] in
  let pushed_args :=
    mapi (fun i '(_, ty) =>
      let arg_rel := tRel (n_args - 1 - i) in
      match ind_of_type ty with
      | None => arg_rel
      | Some ind =>
        match find (fun e =>
                      andb (eq_kername (inductive_mind (snd e)) (inductive_mind ind))
                           (Nat.eqb (inductive_ind (snd e)) (inductive_ind ind)))
                   type_map with
        | Some (kn, _) =>
          if existsb (eq_kername kn) pi_set then
            match find (fun e => eq_kername (fst e) kn) pi_push_map with
            | Some (_, pi_push_fn) => tApp (lift n_args 0 pi_push_fn) [arg_rel]
            | None => arg_rel
            end
          else
            match find (fun e => eq_kername (fst e) kn) push_hole_map with
            | Some (_, sub_push_tm) => tApp (lift n_args 0 sub_push_tm) [arg_rel]
            | None => arg_rel
            end
        | None => arg_rel
        end
      end)
    arg_types_decl in
  let rhs_app :=
    match pushed_args with
    | [] => fn_in
    | _  => tApp fn_in pushed_args
    end in
  let eq_body := tApp eq_ind_tm [old_type; lhs; rhs_app] in
  List.fold_right (fun '(nm, T) acc => tProd nm T acc) eq_body arg_types_decl.

(** True if [s1] is a prefix of [s2] (bytestring version). *)
Fixpoint string_is_prefix (s1 s2 : string) : bool :=
  match s1, s2 with
  | String.EmptyString, _ => true
  | _, String.EmptyString => false
  | String.String c1 r1, String.String c2 r2 =>
    if Byte.eqb c1 c2 then string_is_prefix r1 r2 else false
  end.

(** Collect An-hole metadata from already-quoted [type_minds].
    Returns [(rel_ind, new_ind, cstr_nm, fnSymb_ty)] for every extra constructor
    whose name starts with the relation name (convention: [{relName}An{k}]).
    [rel_ind] carries both the block kername and the relation's body index so that
    [build_an_hole_prop] can construct a valid [tInd] even for mutual relations.
    Order: outer loop is [kn_mode_list], so An-holes are grouped by relation. *)
Definition collect_an_hole_infos
    (type_minds   : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (type_map     : list (kername * inductive))
    (app_kn_map   : list (kername * list term * inductive))
    (kn_mode_list : list (inductive * (string * (list nat * list nat))))
    : list (inductive * inductive * string * term) :=
  List.flat_map (fun '(rel_ind, (rel_nm, _)) =>
    List.flat_map (fun '((old_kn, new_ind), (old_mind, new_mind)) =>
      let n_bodies := List.length new_mind.(ind_bodies) in
      let n_params := new_mind.(ind_npars) in
      let n_old_ctors :=
        match nth_error old_mind.(ind_bodies) 0 with
        | None    => 0
        | Some ob => List.length ob.(ind_ctors)
        end in
      match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
      | None => []
      | Some nob =>
        let extra := List.skipn n_old_ctors nob.(ind_ctors) in
        let matching := filter (fun c => string_is_prefix rel_nm c.(cstr_name)) extra in
        List.map (fun c =>
          let fnSymb_ty := make_fnSymb_type new_ind n_bodies n_params c type_map app_kn_map in
          (rel_ind, new_ind, c.(cstr_name), fnSymb_ty))
        matching
      end)
    type_minds)
  kn_mode_list.

(** Collect metadata for coIndPush holes: one entry per non-pi type in [type_minds]. *)
Definition collect_coind_push_hole_infos
    (type_minds : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (pi_set     : list kername)
    : list (kername * inductive * mutual_inductive_body * mutual_inductive_body) :=
  List.flat_map (fun '((old_kn, new_ind), (old_mind, new_mind)) =>
    if existsb (eq_kername old_kn) pi_set then []
    else [(old_kn, new_ind, old_mind, new_mind)])
  type_minds.

(** Collect metadata for piPushFull holes: one entry per pi_set type in [type_minds]. *)
Definition collect_pi_push_hole_infos
    (type_minds : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (pi_set     : list kername)
    : list (kername * inductive * mutual_inductive_body * mutual_inductive_body) :=
  List.flat_map (fun '((old_kn, new_ind), (old_mind, new_mind)) =>
    if existsb (eq_kername old_kn) pi_set then [(old_kn, new_ind, old_mind, new_mind)]
    else [])
  type_minds.

(** Walk [an_hole_infos] and [an_fn_tms] in lockstep to find the fn_tm
    for the An-hole whose [cstr_nm] matches [target]. *)
Fixpoint find_an_fn_tm (target : ident)
    (an_infos  : list (inductive * inductive * string * term))
    (an_fn_tms : list term)
    : term :=
  match an_infos, an_fn_tms with
  | [], _ | _, [] => tVar "fn_tm_not_found"
  | x :: rest_infos, tm :: rest_tms =>
    let '(((_, _), c_nm), _) := x in
    if String.eqb c_nm target then tm
    else find_an_fn_tm target rest_infos rest_tms
  end.

(** Like [find_an_fn_tm] but returns [None] instead of a fallback term when no match is found. *)
Fixpoint find_an_fn_tm_opt (target : ident)
    (an_infos  : list (inductive * inductive * string * term))
    (an_fn_tms : list term)
    : option term :=
  match an_infos, an_fn_tms with
  | [], _ | _, [] => None
  | x :: rest_infos, tm :: rest_tms =>
    let '(((_, _), c_nm), _) := x in
    if String.eqb c_nm target then Some tm
    else find_an_fn_tm_opt target rest_infos rest_tms
  end.

(** Right-associate a list of prop terms with [/\]. Returns [True] for [[]]. *)
Fixpoint make_conjunction (true_tm and_tm : term) (props : list term) : term :=
  match props with
  | []      => true_tm
  | [p]     => p
  | p :: ps => tApp and_tm [p; make_conjunction true_tm and_tm ps]
  end.

(** Declare [typeNmcoIndPushfnSymb : new_type -> old_type] for each non-pi type. *)
Polymorphic Fixpoint declare_coIndPush_fn_axioms
    (todo       : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (type_map   : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (pi_set     : list kername)
    (cur_mp     : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), _) :: rest =>
    _ <- (if existsb (eq_kername old_kn) pi_set then tmReturn tt
          else
            let old_type := subst_ind_to_old type_map app_kn_map new_ind in
            let new_type := tInd new_ind [] in
            let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
            push_ty_ev <- tmEval all (tProd anon_b new_type old_type) ;;
            tmMkParameter (snd old_kn ++ "coIndPushfnSymb") push_ty_ev) ;;
    declare_coIndPush_fn_axioms rest type_map app_kn_map pi_set cur_mp
  end.

(** Build [forall (h0 : HT0) .. (hn : HTn), prop0 /\ .. /\ propn] and declare
    it as [rel_nm ++ "AnimatedTopFnProp"].  The holes are the wrapper inductives
    for An-holes (one per extra animation constructor) followed by coIndPush holes
    (one per non-pi lifted type).  Each property uses the unwrapped hole rather
    than a global axiom: e.g. [{cstrNm}Symb_unwrap h] instead of [{cstrNm}fnSymb].
    Hole types are deduplicated by wrapper inductive kername so that each unique
    wrapper inductive appears at most once as a forall binder. *)
Polymorphic Definition generate_animated_top_fn_prop
    (rel_nm       : ident)
    (type_minds   : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (type_map     : list (kername * inductive))
    (app_kn_map   : list (kername * list term * inductive))
    (pi_set       : list kername)
    (cur_mp       : modpath)
    (kn_mode_list : list (inductive * (string * (list nat * list nat))))
    (fn_infos     : list (kername * list term * term))
    : TemplateMonad unit :=
  eq_sample   <- tmQuote (0 = 0) ;;
  and_sample  <- tmQuote (True /\ True) ;;
  true_sample <- tmQuote True ;;
  let eq_ind_tm :=
    match eq_sample with
    | tApp f _ => f
    | _         => tVar "eq_not_found"
    end in
  let and_tm :=
    match and_sample with
    | tApp f _ => f
    | _         => tVar "and_not_found"
    end in
  (* Step 1: collect hole metadata in fixed order. *)
  let an_hole_infos      := collect_an_hole_infos type_minds type_map app_kn_map kn_mode_list in
  let push_hole_infos    := collect_coind_push_hole_infos type_minds pi_set in
  let pi_push_hole_infos := collect_pi_push_hole_infos type_minds pi_set in
  let n_an      := List.length an_hole_infos in
  let n_push    := List.length push_hole_infos in
  let n_pi_push := List.length pi_push_hole_infos in
  (* Step 2: build hole-type terms (An-holes first, then coIndPush, then piPushFull).
     fold_right makes the last element innermost (tRel 0): piPushFull holes are
     innermost, coIndPush next, An-holes outermost. *)
  let anon_b := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let an_hole_types :=
    List.map (fun x =>
      let '(((_, _), cstr_nm), _) := x in
      tInd {| inductive_mind := (cur_mp, cstr_nm ++ "Symb"); inductive_ind := 0 |} [])
    an_hole_infos in
  let push_hole_types :=
    List.map (fun x =>
      let '(((old_kn, _), _), _) := x in
      tInd {| inductive_mind := (cur_mp, snd old_kn ++ "coIndPushSymb"); inductive_ind := 0 |} [])
    push_hole_infos in
  let pi_push_hole_types :=
    List.map (fun '(((old_kn, _), _), _) =>
      tInd {| inductive_mind := (cur_mp, snd old_kn ++ "PushFullSymb"); inductive_ind := 0 |} [])
    pi_push_hole_infos in
  let hole_types_raw :=
    List.app an_hole_types (List.app push_hole_types pi_push_hole_types) in
  (* Deduplicate by wrapper inductive kername so each unique hole type gets
     exactly one forall binder.  canon_map.(i) is the canonical index in
     unique_hole_types for the i-th entry of hole_types_raw.
     canon_rel i = tRel-depth for entry i under the deduplicated binder list. *)
  let '(unique_hole_types, canon_map) := dedup_hole_types hole_types_raw in
  let n_unique := List.length unique_hole_types in
  let canon_rel (k : nat) := n_unique - 1 - nth k canon_map 0 in
  (* Step 3: fn_tms for An-holes — use canonical depth. *)
  let an_fn_tms :=
    mapi (fun i x =>
      let '(((_, _), cstr_nm), _) := x in
      let unwrap_c := tConst (cur_mp, cstr_nm ++ "Symb_unwrap") [] in
      tApp unwrap_c [tRel (canon_rel i)])
    an_hole_infos in
  (* Step 4: coIndPush holes — canonical offset = n_an + j. *)
  let push_hole_map :=
    mapi (fun j x =>
      let '(((old_kn, _), _), _) := x in
      let unwrap_c := tConst (cur_mp, snd old_kn ++ "coIndPushSymb_unwrap") [] in
      (old_kn, tApp unwrap_c [tRel (canon_rel (n_an + j))]))
    push_hole_infos in
  let push_tms := List.map snd push_hole_map in
  (* Step 4b: piPushFull holes — canonical offset = n_an + n_push + j. *)
  let pi_push_map :=
    mapi (fun j '(((old_kn, _), _), _) =>
      let unwrap_c := tConst (cur_mp, snd old_kn ++ "PushFullSymb_unwrap") [] in
      (old_kn, tApp unwrap_c [tRel (canon_rel (n_an + n_push + j))]))
    pi_push_hole_infos in
  let pi_push_tms := List.map snd pi_push_map in
  (* Step 5: build An-hole props. *)
  let an_props :=
    mapi (fun i x =>
      let '(((rel_ind, new_ind), _), fnSymb_ty) := x in
      let fn_tm := nth i an_fn_tms (tVar "an_fn_not_found") in
      build_an_hole_prop rel_ind new_ind fn_tm fnSymb_ty)
    an_hole_infos in
  (* Map from LiftedCstr ctor name -> original function kername.
     LiftedCstr ctors are named [snd fn_kn ++ "LiftedCstr"], so stripping that
     suffix and looking up in fn_infos recovers the original function. *)
  let lifted_ctor_fn_map :=
    List.map (fun fi => (snd (fst (fst fi)) ++ "LiftedCstr", fst (fst fi)))
    fn_infos in
  (* Build the extra-ctor equation for a single ctor beyond n_old_ctors.
     - Animation ctor (in an_hole_infos): RHS uses the unwrapped An-hole.
     - LiftedCstr ctor (in lifted_ctor_fn_map): RHS uses the concrete original function
       applied to recursively pushed arguments — same builder, different fn_tm.
     - Unknown extra ctor: skip (should not occur in a well-formed lifting). *)
  let build_extra_prop (push_tm : term) (old_kn : kername) (new_ind : inductive)
      (new_kn : kername) (n_bodies : nat) (ctor_idx : nat) (new_ctor : constructor_body)
      (old_type : term) : list term :=
    let nm := new_ctor.(cstr_name) in
    match find_an_fn_tm_opt nm an_hole_infos an_fn_tms with
    | Some fn_tm =>
      [build_coIndPush_eq_for_extra_ctor
         old_kn new_ind new_kn n_bodies ctor_idx new_ctor
         type_map pi_set push_tm push_hole_map pi_push_map fn_tm eq_ind_tm old_type]
    | None =>
      match find (fun e => String.eqb (fst e) nm) lifted_ctor_fn_map with
      | Some (_, fn_kn) =>
        let fn_tm := tConst fn_kn [] in
        [build_coIndPush_eq_for_extra_ctor
           old_kn new_ind new_kn n_bodies ctor_idx new_ctor
           type_map pi_set push_tm push_hole_map pi_push_map fn_tm eq_ind_tm old_type]
      | None => []
      end
    end in
  (* Step 6: build coIndPush props (regular + all extra ctors for each push hole).
     pi_push_map now carries tRel references to PushFullSymb holes.
     Animation ctors use An-hole unwrap; LiftedCstr ctors use the concrete function. *)
  let push_props :=
    List.concat (mapi (fun j x =>
      let '(((old_kn, new_ind), old_mind), new_mind) := x in
      let new_kn   := inductive_mind new_ind in
      let n_bodies := List.length new_mind.(ind_bodies) in
      let old_type := subst_ind_to_old type_map app_kn_map new_ind in
      let push_tm  := nth j push_tms (tVar "push_tm_not_found") in
      match nth_error new_mind.(ind_bodies) (inductive_ind new_ind),
            nth_error old_mind.(ind_bodies) (inductive_ind new_ind) with
      | Some new_oib, Some old_oib =>
        let n_old_ctors := List.length old_oib.(ind_ctors) in
        let regular_props :=
          mapi (fun ctor_idx new_ctor =>
            build_coIndPush_eq_for_ctor
              old_kn new_ind new_kn n_bodies ctor_idx new_ctor
              type_map pi_set push_tm push_hole_map pi_push_map eq_ind_tm old_type)
          (List.firstn n_old_ctors new_oib.(ind_ctors)) in
        let extra_props :=
          List.concat (mapi (fun i new_ctor =>
            build_extra_prop push_tm old_kn new_ind new_kn n_bodies (n_old_ctors + i)
              new_ctor old_type)
          (List.skipn n_old_ctors new_oib.(ind_ctors))) in
        List.app regular_props extra_props
      | _, _ => []
      end)
    push_hole_infos) in
  (* Step 6b: build piPushFull props — one equation per ctor of each pi_set lifted type.
     Regular (lifted-old) ctors use recursive PushFullSymb calls.
     Animation ctors delegate to the corresponding An-hole.
     LiftedCstr ctors (e.g. substLiftedCstr) use the concrete original function
     applied to recursively pushed arguments — no hole needed for these. *)
  let pi_push_props :=
    List.concat (mapi (fun j x =>
      let '(((old_kn, new_ind), old_mind), new_mind) := x in
      let new_kn   := inductive_mind new_ind in
      let n_bodies := List.length new_mind.(ind_bodies) in
      let old_type := subst_ind_to_old type_map app_kn_map new_ind in
      let push_tm  := nth j pi_push_tms (tVar "pi_push_tm_not_found") in
      match nth_error new_mind.(ind_bodies) (inductive_ind new_ind),
            nth_error old_mind.(ind_bodies) (inductive_ind new_ind) with
      | Some new_oib, Some old_oib =>
        let n_old_ctors := List.length old_oib.(ind_ctors) in
        let regular_props :=
          mapi (fun ctor_idx new_ctor =>
            build_coIndPush_eq_for_ctor
              old_kn new_ind new_kn n_bodies ctor_idx new_ctor
              type_map pi_set push_tm push_hole_map pi_push_map eq_ind_tm old_type)
          (List.firstn n_old_ctors new_oib.(ind_ctors)) in
        let extra_props :=
          List.concat (mapi (fun i new_ctor =>
            build_extra_prop push_tm old_kn new_ind new_kn n_bodies (n_old_ctors + i)
              new_ctor old_type)
          (List.skipn n_old_ctors new_oib.(ind_ctors))) in
        List.app regular_props extra_props
      | _, _ => []
      end)
    pi_push_hole_infos) in
  (* Step 7: conjoin all props and wrap in foralls over all hole types. *)
  let conjoined := make_conjunction true_sample and_tm
    (List.app an_props (List.app push_props pi_push_props)) in
  let prop_tm :=
    List.fold_right (fun ht acc => tProd anon_b ht acc) conjoined unique_hole_types in
  all_ev <- tmEval all prop_tm ;;
  tmMkDefinition (rel_nm ++ "AnimatedTopFnProp") all_ev.

(** Like [animate_coinductive_opaque_sigma] but the holes in the output are
    function-typed and named: each animation constructor position gets a wrapper
    inductive [ctorNameSymb] around the original-type function, and each
    coinductive-push position gets a wrapper inductive [typeNmcoIndPushSymb].
    The final composite is [rel_nm ++ "TransparentSigmaAnimatedTopFn"] and
    uses [rel_nm ++ "TransparentSigmaOutputPush"]. *)
Unset Universe Checking.
Polymorphic Definition animate_coinductive_transparent_sigma
    (rel_kn : kername)
    (modes  : mode_map)
    (fuel   : nat)
    : TemplateMonad unit :=
  let rel_nm := snd rel_kn in
  kn_mode_list <- monad_fold_left (fun acc me =>
    refs <- tmLocate (fst me) ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [(ind, me)])
    | _ => tmFail ("animate_coinductive_transparent_sigma: cannot find '" ++ fst me ++ "'")
    end)
    modes [] ;;
  match kn_mode_list return TemplateMonad unit with
  | [] => @tmFail unit "animate_coinductive_transparent_sigma: no modes provided"
  | _  =>
    preproc_result <- preprocess_coind_types modes fuel ;;
    preproc_result <- tmEval all preproc_result ;;
    let type_mapping   := fst preproc_result in
    let app_kn_mapping := snd preproc_result in
    cur_mp <- tmCurrentModPath tt ;;
    let unique_block_kns :=
      fold_left (fun acc p =>
        if existsb (eq_kername (inductive_mind (fst p))) acc then acc
        else List.app acc [inductive_mind (fst p)])
      kn_mode_list [] in
    let rel_mapping :=
      List.map (fun kn =>
        (kn, {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |}))
        unique_block_kns in
    _ <- generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp ;;
    rel_block_minds_assoc <- monad_map (fun kn =>
      mind <- tmQuoteInductive kn ;;
      tmReturn (kn, mind))
      unique_block_kns ;;
    rel_block_minds_assoc <- tmEval all rel_block_minds_assoc ;;
    let block_id_map := List.map (fun kn => (kn, kn)) unique_block_kns in
    let sorted_block_kns :=
      topo_sort_kns unique_block_kns rel_block_minds_assoc block_id_map
                    [] [] (S #|unique_block_kns|) in
    prod_refs <- tmLocate "prod" ;;
    anim_refs <- tmLocate "animation_result" ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) prod_refs,
          find (fun g => match g with IndRef _ => true | _ => false end) anim_refs with
    | Some (IndRef prod_ind), Some (IndRef anim_ind) =>
      let prod_kn     := inductive_mind prod_ind in
      let anim_res_kn := inductive_mind anim_ind in
      _ <- generate_push_params type_mapping type_mapping app_kn_mapping ;;
      npi_set <- compute_npi_fix type_mapping [] (List.length type_mapping + 1) ;;
      npi_set <- tmEval all npi_set ;;
      let pi_set :=
        List.map fst (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set)) type_mapping) in
      type_minds <- monad_map (fun entry =>
        old_mind <- tmQuoteInductive (fst entry) ;;
        new_mind <- tmQuoteInductive (inductive_mind (snd entry)) ;;
        tmReturn (entry, (old_mind, new_mind)))
        type_mapping ;;
      type_minds <- tmEval all type_minds ;;
      hr_hole_tm  <- tmQuote (hr_hole) ;;
      hr_pure_tm  <- tmQuote (hr_pure) ;;
      hr_ap_tm    <- tmQuote (hr_ap) ;;
      hr_map_tm   <- tmQuote (hr_map) ;;
      hr_type_tm  <- tmQuote (HoleyResult) ;;
      hr_pair_tm  <- tmQuote (hr_pair) ;;
      (* Standard push and plain push (needed by liftedFunc and other parts of pipeline). *)
      _ <- generate_push_fns_plain type_minds type_mapping app_kn_mapping pi_set cur_mp ;;
      _ <- generate_push_fns type_minds type_mapping app_kn_mapping pi_set cur_mp
                              hr_hole_tm hr_pure_tm hr_ap_tm hr_type_tm ;;
      _ <- generate_chk_fns type_minds type_mapping pi_set cur_mp ;;
      _ <- generate_eqfn_defs type_minds type_mapping pi_set cur_mp ;;
      let all_fn_infos_base :=
        flat_map (fun km =>
          let n_params := (snd km).(ind_npars) in
          flat_map (fun oib =>
            let idx_types := extract_arg_types n_params 100 oib.(ind_type) in
            flat_map (fun c =>
              collect_fn_app_info_from_ctor idx_types rel_block_minds_assoc c)
                     oib.(ind_ctors))
          (snd km).(ind_bodies))
        rel_block_minds_assoc in
      let unique_fn_infos_base :=
        fold_left (fun acc entry =>
          let fkn := fst (fst entry) in
          if existsb (fun e => eq_kername (fst (fst e)) fkn) acc
          then acc
          else List.app acc [entry])
        all_fn_infos_base [] in
      unique_fn_infos_base <- tmEval all unique_fn_infos_base ;;
      let extra_fn_pairs_r :=
        flat_map (fun km =>
          flat_map (fun oib =>
            flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
          (snd km).(ind_bodies))
        rel_block_minds_assoc in
      let new_fn_pairs_r :=
        fold_left (fun acc p =>
          let fn_kn := fst p in
          if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) unique_fn_infos_base)
                 (existsb (fun q => eq_kername (fst q) fn_kn) acc)
          then acc
          else List.app acc [p])
        extra_fn_pairs_r [] in
      new_fn_pairs_r <- tmEval all new_fn_pairs_r ;;
      extra_fn_infos_r <- monad_map (fun p =>
        let fn_kn := fst p in
        let n     := List.length (snd p) in
        cb <- tmQuoteConstant fn_kn false ;;
        let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
        tmReturn (fn_kn, decl_arg_types, ret_tp)) new_fn_pairs_r ;;
      extra_fn_infos_r <- tmEval all extra_fn_infos_r ;;
      let unique_fn_infos := List.app unique_fn_infos_base extra_fn_infos_r in
      unique_fn_infos <- tmEval all unique_fn_infos ;;
      _ <- generate_lifted_fns unique_fn_infos type_mapping app_kn_mapping cur_mp ;;
      let fn_kn_map :=
        List.map (fun fi => (fst (fst fi), (cur_mp, snd (fst (fst fi)) ++ "liftedFunc")))
                 unique_fn_infos in
      _ <- monad_fold_left (fun _ block_kn =>
        let block_modes :=
          List.map snd (filter (fun p => eq_kername (inductive_mind (fst p)) block_kn) kn_mode_list) in
        lift_relation block_kn rel_mapping type_mapping app_kn_mapping block_modes fn_kn_map)
        sorted_block_kns tt ;;
      _ <- generate_inputLift_fns kn_mode_list type_mapping app_kn_mapping
                                   prod_kn anim_res_kn cur_mp ;;
      _ <- generate_rest_fns kn_mode_list cur_mp prod_kn ;;
      (* Generate fnSymb wrapper inductives (ctorNameSymb for animation ctor holes). *)
      _ <- generate_fnSymb_wrapper_inductives type_mapping type_mapping app_kn_mapping cur_mp ;;
      (* Generate wrapper inductives for push holes: coIndPushSymb (non-pi) and PushFullSymb (pi). *)
      _ <- generate_pushSymb_wrapper_inductives type_minds type_mapping app_kn_mapping
                                                pi_set cur_mp "coIndPushSymb" false ;;
      _ <- generate_pushSymb_wrapper_inductives type_minds type_mapping app_kn_mapping
                                                pi_set cur_mp "PushFullSymb" true ;;
      (* Transparent sigma push functions: body takes hole values, wrapper holds static hole list.
         Sort so pi-set types (whose bodies reference no other bodies) come first. *)
      let type_minds_pi_first :=
        List.app
          (List.filter (fun '((old_kn, _), _) => existsb (eq_kername old_kn) pi_set) type_minds)
          (List.filter (fun '((old_kn, _), _) => negb (existsb (eq_kername old_kn) pi_set)) type_minds) in
      _ <- generate_transparent_sigma_push_fns type_minds_pi_first type_mapping app_kn_mapping pi_set cur_mp
                      hr_hole_tm hr_pure_tm hr_ap_tm hr_map_tm hr_type_tm [] ;;
      (* Output push for the transparent sigma version. *)
      _ <- generate_transparent_sigma_outputPush_fns kn_mode_list type_mapping app_kn_mapping pi_set
                              prod_kn anim_res_kn cur_mp hr_type_tm hr_pair_tm hr_pure_tm ;;
      (* Animate the lifted relation. *)
      let lifted_kn    := (cur_mp, rel_nm ++ "'") in
      let lifted_modes := List.map (fun me => (fst me ++ "'", snd me)) modes in
      _ <- animate_coinductive lifted_kn lifted_modes fuel ;;
      (* Build the composite: fun n inp => TransparentSigmaOutputPush n (AnimFn n (InputLift inp)) *)
      top_mind <- tmQuoteInductive rel_kn ;;
      match find (fun me => String.eqb (fst me) rel_nm) modes,
            find (fun ob => String.eqb ob.(ind_name) rel_nm) top_mind.(ind_bodies) with
      | Some (_, (in_pos, out_pos)), Some top_oib =>
        let n_params  := top_mind.(ind_npars) in
        let n_total   := List.length in_pos + List.length out_pos in
        let all_types := extract_arg_types n_params n_total top_oib.(ind_type) in
        prod_refs2 <- tmLocate "prod" ;;
        anim_refs2 <- tmLocate "animation_result" ;;
        match find (fun g => match g with IndRef _ => true | _ => false end) prod_refs2,
              find (fun g => match g with IndRef _ => true | _ => false end) anim_refs2 with
        | Some (IndRef prod_ind2), Some (IndRef anim_ind2) =>
          let prod_kn2     := inductive_mind prod_ind2 in
          let anim_res_ind := {| inductive_mind := inductive_mind anim_ind2; inductive_ind := 0 |} in
          let nat_ind      := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
          let anon_b       := {| binder_name := nAnon; binder_relevance := Relevant |} in
          let in_types     := List.map (fun p => nth p all_types (tVar "?")) in_pos in
          let in_type      := match in_types with [t] => t | _ => make_prod_type prod_kn2 in_types end in
          let anim_in_type := tApp (tInd anim_res_ind []) [in_type] in
          let inputLift_fn            := tConst (cur_mp, rel_nm ++ "inputLift") [] in
          let transparentSigmaPush_fn := tConst (cur_mp, rel_nm ++ "TransparentSigmaOutputPush") [] in
          let animFn                  := tConst (cur_mp, rel_nm ++ "'" ++ top_fn_suffix) [] in
          let composite :=
            tLambda anon_b (tInd nat_ind [])
            (tLambda anon_b anim_in_type
            (tApp transparentSigmaPush_fn
              [tRel 1;
               tApp animFn [tRel 1; tApp inputLift_fn [tRel 0]]]))
          in
          _ <- generate_animated_top_fn_prop
                  rel_nm type_minds type_mapping app_kn_mapping pi_set cur_mp
                  kn_mode_list unique_fn_infos ;;
          tmMkDefinition (rel_nm ++ "TransparentSigmaAnimatedTopFn") composite
        | _, _ =>
          tmFail "animate_coinductive_transparent_sigma: cannot locate prod or animation_result (2)"
        end
      | None, _ => tmFail ("animate_coinductive_transparent_sigma: no mode entry for " ++ rel_nm)
      | _, None  => tmFail ("animate_coinductive_transparent_sigma: cannot find body " ++ rel_nm)
      end
    | _, _ => @tmFail unit "animate_coinductive_transparent_sigma: cannot locate prod or animation_result"
    end
  end.
Set Universe Checking.
