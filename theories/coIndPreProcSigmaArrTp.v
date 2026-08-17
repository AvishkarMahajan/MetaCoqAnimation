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

(** Like [collect_eq_arg_kns] but collects arrow types (tProd) T from
    equality premises [eq T _ _].  Used to seed the arrow lifting set with
    arrow types that appear as equality types in constructor premises. *)
Fixpoint collect_eq_arg_arrows (t : term) : list term :=
  match t with
  | tApp f args =>
    let eq_hits :=
      match f with
      | tInd {| inductive_mind := kn |} _ =>
        if String.eqb (snd kn) "eq" then
          match args with
          | T :: _ => match T with tProd _ _ _ => [T] | _ => [] end
          | []     => []
          end
        else []
      | _ => []
      end in
    eq_hits ++ collect_eq_arg_arrows f ++ flat_map collect_eq_arg_arrows args
  | tProd   _ ty body
  | tLambda _ ty body   => collect_eq_arg_arrows ty ++ collect_eq_arg_arrows body
  | tLetIn  _ v ty body =>
    collect_eq_arg_arrows v ++ collect_eq_arg_arrows ty ++ collect_eq_arg_arrows body
  | tCase _ pred disc brs =>
    flat_map collect_eq_arg_arrows pred.(pparams) ++
    collect_eq_arg_arrows pred.(preturn) ++
    collect_eq_arg_arrows disc ++
    flat_map (fun br => collect_eq_arg_arrows br.(bbody)) brs
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
                    (* cstr_args.decl_type has params as free vars at tRel(j+outer) — params
                       precede body self-refs in the cstr_args de Bruijn scope.
                       Normalise tInd self-refs first, then substitute params at k=outer. *)
                    let d0 := subst_self_ref old_kn outer d.(decl_type) in
                    let t0 := subst concrete_args outer d0 in
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

(** Structural equality on terms, ignoring binder names (nAnon vs nNamed).
    Used to match arrow types like [nat->nat] regardless of binder annotation. *)
Fixpoint rfp_eqb_term (t1 t2 : term) : bool :=
  match t1, t2 with
  | tRel i,          tRel j             => Nat.eqb i j
  | tVar x,          tVar y             => String.eqb x y
  | tConst c1 _,     tConst c2 _        => eq_kername c1 c2
  | tInd i1 _,       tInd i2 _          =>
    andb (eq_kername (inductive_mind i1) (inductive_mind i2))
         (Nat.eqb (inductive_ind i1) (inductive_ind i2))
  | tConstruct i1 k1 _, tConstruct i2 k2 _ =>
    andb (eq_kername (inductive_mind i1) (inductive_mind i2))
    (andb (Nat.eqb (inductive_ind i1) (inductive_ind i2)) (Nat.eqb k1 k2))
  | tSort _,         tSort _            => true
  | tProd _ a1 b1,   tProd _ a2 b2
  | tLambda _ a1 b1, tLambda _ a2 b2   =>
    andb (rfp_eqb_term a1 a2) (rfp_eqb_term b1 b2)
  | tApp f1 as1,     tApp f2 as2        =>
    andb (rfp_eqb_term f1 f2)
    (andb (Nat.eqb #|as1| #|as2|)
    ((fix eqb_args (l1 l2 : list term) : bool :=
        match l1, l2 with
        | [],       []       => true
        | a1 :: r1, a2 :: r2 => andb (rfp_eqb_term a1 a2) (eqb_args r1 r2)
        | _,        _        => false
        end) as1 as2))
  | _, _ => false
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
    (arr_mapping            : list (term * inductive))
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
                let raw_t := d.(decl_type) in
                let t :=
                  match find (fun p => rfp_eqb_term (fst p) raw_t) arr_mapping with
                  | Some (_, new_ind) => tInd new_ind []
                  | None =>
                    subst_idx_type old_kn self_base ext app_kn_mapping
                      spec_unlifted_kn_map depth raw_t
                  end in
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
    (add_lift_cstr        : bool)
    (arr_mapping          : list (term * inductive))
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
    | _ =>
      match find (fun p => rfp_eqb_term (fst p) tp) arr_mapping with
      | Some (_, new_ind) => tInd new_ind []
      | None              => tp
      end
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
    | _ => existsb (fun p => rfp_eqb_term (fst p) tp) arr_mapping
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
                        app_kn_mapping spec_unlifted_kn_map modes_with_idx arr_mapping in
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
              lifted_ctors
              (* Sigma2: LiftCstr constructor — typeNameLiftCstr : old_type -> new_type.
                 Only for non-pi (originally CoFinite) types. No step3 needed since
                 the arg type is the original type (not in the new block). *)
              ++ (if andb add_lift_cstr
                          (match old_mind.(ind_finite) with CoFinite => true | _ => false end)
                  then
                    let block_body_idx := block_body_offset + i in
                    let n_par          := #|params'| in
                    let old_type_i     := tInd {| inductive_mind := old_kn; inductive_ind := i |} [] in
                    let lift_arg       := {| decl_name := anon_b; decl_body := None;
                                             decl_type := old_type_i |} in
                    let return_t :=
                      if Nat.eqb n_par 0 then tRel (block_n_bodies - block_body_idx)
                      else tApp (tRel (n_par + 1 + block_n_bodies - 1 - block_body_idx))
                                (List.map tRel (List.rev (seq 1 n_par))) in
                    [{| cstr_name    := oib.(ind_name) ++ "LiftCstr";
                        cstr_args    := [lift_arg];
                        cstr_indices := [];
                        cstr_type    := it_mkProd_or_LetIn (List.app params' [lift_arg]) return_t;
                        cstr_arity   := 1 |}]
                  else []);
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
            flat_map (fun ik =>
              flat_map (fun ok =>
                if eq_kername ok ik then [] else [(ik, ok)])
              out_kns)
            in_kns in
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
    [(in_kn, out_kn)] for [lat_unified_closure_step] (i2i direction):
    if the input type is in sigma2, the output type is added.
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
        flat_map (fun ik => flat_map (fun ok =>
          if eq_kername ok ik then [] else [(ik, ok)]) out_kns) in_kns
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
          flat_map (fun ik => flat_map (fun ok =>
            if eq_kername ok ik then [] else [(ik, ok)]) out_kns) in_kns)
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
    (sigma2      : bool)
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
          pre_app_kn_mapping spec_kn_pairs modes_with_idx fn_app_infos 1 0 sigma2 [] in
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
  _ <- (if sigma2 then tmReturn tt
        else
    monad_fold_left (fun _ grp =>
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
    orig_groups tt) ;;
  (* Split groups that mix Finite and CoFinite types: Rocq forbids mixed
     mutual blocks, and a group whose first member is Finite would silently
     make a CoInductive type (e.g. stream') appear as Inductive.
     In sigma2 mode all types are forced to Finite so no splitting needed. *)
  let groups :=
    if sigma2 then orig_groups
    else
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
                       block_n_bodies block_body_offset sigma2 [] in
            (S block_body_offset, List.app bodies_so_far m.(ind_bodies))
          end)
        grp (0, [])) in
      let block_finite :=
        if sigma2 then Finite
        else match find (fun p => eq_kername (fst p) first_kn) type_minds with
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

(** Structural equality on terms ignoring binder names.
    Used throughout the arrow-type lifting pipeline for matching [tProd] patterns. *)
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
    (arr_body_map   : list (term * (inductive * list constructor_body)))
    : list constructor_body :=
  match find (fun mwi => String.eqb (fst (fst mwi)) oib.(ind_name)) modes_with_idx with
  | None => []
  | Some mwi =>
    let in_pos   := fst (snd (fst mwi)) in
    let out_pos  := snd (snd (fst mwi)) in
    let idx_ctx  := snd mwi in
    let n_idx    := #|idx_ctx| in
    let n_inputs := #|in_pos| in
    (* Reconstruct arr_subst from arr_body_map to lift arrow-type input positions. *)
    let arr_subst' :=
      List.map (fun '(arr_t, (fn_ind, _)) => (arr_t, tInd fn_ind [])) arr_body_map in
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
                  match find (fun p => rfp_eqb_term (fst p) d.(decl_type)) arr_subst' with
                  | Some (_, repl) => repl
                  | None => subst_inds_and_ctors app_kn_mapping type_mapping d.(decl_type)
                  end |}])
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
              (* Arrow-type output position: lifted to fnTypeN by arr_body_map. *)
              match find (fun p => rfp_eqb_term (fst p) d.(decl_type)) arr_body_map with
              | Some (_, (fn_ind, fn_ctors)) =>
                let ctor_idx :=
                  match find_ctor_idx extra_nm fn_ctors 0 with
                  | Some i => i | None => 0
                  end in
                if Nat.eqb n_inputs 0
                then tConstruct fn_ind ctor_idx []
                else tApp (tConstruct fn_ind ctor_idx []) input_var_list
              | None =>
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
              end (* end arr_body_map match *)
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

(** Recursively substitute terms matching [arr_subst] entries.
    Applied before [subst_inds_and_ctors] in the relation lifting pipeline
    to replace arrow-type parameters (e.g. [nat->nat]) with their lifted
    inductive equivalents (e.g. [fnType0]). *)
Fixpoint subst_arrow_terms (arr_subst : list (term * term)) (t : term) : term :=
  match find (fun p => rfp_eqb_term (fst p) t) arr_subst with
  | Some (_, replacement) => replacement
  | None =>
    match t with
    | tProd na ty body =>
      tProd na (subst_arrow_terms arr_subst ty) (subst_arrow_terms arr_subst body)
    | tApp f args =>
      tApp (subst_arrow_terms arr_subst f) (List.map (subst_arrow_terms arr_subst) args)
    | tLambda na ty body =>
      tLambda na (subst_arrow_terms arr_subst ty) (subst_arrow_terms arr_subst body)
    | tLetIn na val ty body =>
      tLetIn na (subst_arrow_terms arr_subst val)
                (subst_arrow_terms arr_subst ty)
                (subst_arrow_terms arr_subst body)
    | tCase ci pred disc branches =>
      tCase ci pred (subst_arrow_terms arr_subst disc)
        (List.map (fun br =>
          {| bcontext := br.(bcontext);
             bbody    := subst_arrow_terms arr_subst br.(bbody) |}) branches)
    | tFix mfix idx =>
      tFix (List.map (fun d =>
        {| dname := d.(dname);
           dtype := subst_arrow_terms arr_subst d.(dtype);
           dbody := subst_arrow_terms arr_subst d.(dbody);
           rarg  := d.(rarg) |}) mfix) idx
    | _ => t
    end
  end.

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
    (arr_subst      : list (term * term))
    (arr_body_map   : list (term * (inductive * list constructor_body)))
    (force_finite   : bool)
    : mutual_inductive_body :=
  let new_rel_ind  := {| inductive_mind := new_rel_kn; inductive_ind := 0 |} in
  let full_mapping := (old_rel_kn, new_rel_ind) :: rel_mapping ++ type_mapping in
  let sub_ty t :=
    subst_const_kns fn_kn_map
      (subst_inds_and_ctors app_kn_mapping full_mapping
        (subst_arrow_terms arr_subst t)) in
  let sub_decl d :=
    subst_const_kns_decl fn_kn_map
      (subst_inds_and_ctors_decl app_kn_mapping full_mapping
        {| decl_name := d.(decl_name);
           decl_body := option_map (subst_arrow_terms arr_subst) d.(decl_body);
           decl_type := subst_arrow_terms arr_subst d.(decl_type) |}) in
  let params'  := List.map sub_decl old_mind.(ind_params) in
  let n_params := #|params'| in
  let n_bodies := #|old_mind.(ind_bodies)| in
  {| ind_finite    := if force_finite then Finite else old_mind.(ind_finite);
     ind_npars     := old_mind.(ind_npars);
     ind_universes := old_mind.(ind_universes);
     ind_variance  := old_mind.(ind_variance);
     ind_params    := params';
     ind_bodies    :=
       mapi (fun i oib =>
         let undef :=
           compute_undefined_cstr oib i n_params n_bodies
             type_mapping app_kn_mapping modes_with_idx type_body_map arr_body_map in
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
    [modes_with_idx] supplies pre-computed input/output positions paired with
    index contexts; call [lift_relation] (below) if you only have [mode_map]. *)
Polymorphic Definition lift_relation_mwi
    (rel_kn         : kername)
    (rel_mapping    : list (kername * inductive))
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    (fn_kn_map      : list (kername * kername))
    (arr_subst      : list (term * term))
    (force_finite   : bool)
    : TemplateMonad unit :=
  cur_mp   <- tmCurrentModPath tt ;;
  old_mind <- tmQuoteInductive rel_kn ;;
  let new_rel_kn := (cur_mp, snd rel_kn ++ "'") in
  type_body_map <- monad_map (fun p =>
    let new_ind := snd p in
    new_mind <- tmQuoteInductive (inductive_mind new_ind) ;;
    match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
    | Some oib => tmReturn (new_ind, oib)
    | None     => @tmFail (inductive * one_inductive_body) "lift_relation_mwi: empty lifted type"
    end)
    type_mapping ;;
  arr_body_map <- monad_map (fun '(arr_t, fn_type_t) =>
    match fn_type_t with
    | tInd fn_ind _ =>
      fn_mind <- tmQuoteInductive (inductive_mind fn_ind) ;;
      let fn_ctors :=
        match nth_error fn_mind.(ind_bodies) 0 with
        | Some oib => oib.(ind_ctors) | None => []
        end in
      tmReturn (arr_t, (fn_ind, fn_ctors))
    | _ => tmReturn (arr_t, ({| inductive_mind := (cur_mp, ""); inductive_ind := 0 |}, []))
    end) arr_subst ;;
  lifted_rel_mind <- tmEval all
    (make_lifted_relation_mind old_mind rel_kn new_rel_kn rel_mapping type_mapping
       app_kn_mapping modes_with_idx type_body_map fn_kn_map arr_subst arr_body_map force_finite) ;;
  tmMkInductivePreserveFinite lifted_rel_mind.

(** Backward-compat wrapper: builds [modes_with_idx] from [modes] and the
    quoted inductive, then delegates to [lift_relation_mwi]. *)
Polymorphic Definition lift_relation
    (rel_kn         : kername)
    (rel_mapping    : list (kername * inductive))
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (modes          : mode_map)
    (fn_kn_map      : list (kername * kername))
    (arr_subst      : list (term * term))
    (force_finite   : bool)
    : TemplateMonad unit :=
  old_mind <- tmQuoteInductive rel_kn ;;
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
  lift_relation_mwi rel_kn rel_mapping type_mapping app_kn_mapping
                    modes_with_idx fn_kn_map arr_subst force_finite.


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
    (old_kn        : kername)
    (oib           : one_inductive_body)
    (new_ind       : inductive)
    (type_map      : list (kername * inductive))
    (app_kn_map    : list (kername * list term * inductive))
    (cur_mp        : modpath)
    (orig_form     : option (kername * list term))
    (fix_size      : nat)
    (fix_idx       : nat)
    (kn_to_fix_idx : list (kername * nat))
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
            tApp (tRel (fix_size + n_args - fix_idx)) [tRel snoc_i]
          | Some (Some kn) =>
            let fn_ref :=
              match find (fun p => eq_kername (fst p) kn) kn_to_fix_idx with
              | Some (_, k) => tRel (fix_size + n_args - k)
              | None => tConst (cur_mp, snd kn ++ "Lift") []
              end in
            tApp fn_ref [tRel snoc_i]
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

(** Build the [def term] for the sigma2 depth-parameterised lift of [old_kn].
    Type: [nat -> old_type -> new_type]; structural on [nat] (rarg = 0).
    - At depth O: embed the old value via [typeNameLiftCstr].
    - At depth (S d): match old_type constructors and recursively lift each
      arg; pass [d] to non-pi lifts (kn in [npi_set]) and call pi lifts
      without depth.
    De Bruijn inside the S-branch inner case branch with [n_args] args:
      tRel 0..n_args-1  = ctor args (snoc order, innermost-first)
      tRel n_args        = d (predecessor, from S binder)
      tRel (n_args+1)   = s (old value, from second lambda)
      tRel (n_args+2)   = depth (nat, from first lambda)
      tRel (n_args+3)   = fix self-ref *)
Definition make_lift_def_sigma2
    (old_kn        : kername)
    (oib           : one_inductive_body)
    (new_ind       : inductive)
    (all_map       : list (kername * inductive))
    (app_kn_map    : list (kername * list term * inductive))
    (cur_mp        : modpath)
    (orig_form     : option (kername * list term))
    (npi_set       : list kername)
    (lift_cstr_idx : nat)
    (fix_size      : nat)
    (fix_idx       : nat)
    (kn_to_fix_idx : list (kername * nat))
    : def term :=
  let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let old_ind  := {| inductive_mind := old_kn; inductive_ind := 0 |} in
  let case_ind :=
    match orig_form with
    | None              => old_ind
    | Some (head_kn, _) => {| inductive_mind := head_kn; inductive_ind := 0 |}
    end in
  let n_par     :=
    match orig_form with None => 0 | Some (_, aks) => List.length aks end in
  let par_terms :=
    match orig_form with
    | None                => []
    | Some (_, arg_terms) => arg_terms
    end in
  let old_type :=
    match orig_form with
    | None   => tInd old_ind []
    | Some _ => match par_terms with
                | [] => tInd case_ind []
                | _  => tApp (tInd case_ind []) par_terms
                end
    end in
  let new_type    := tInd new_ind [] in
  let nat_ind_ref := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
  let nat_ci      := {| ci_ind := nat_ind_ref; ci_npar := 0; ci_relevance := Relevant |} in
  let nat_pred    := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := new_type |} in
  let old_pred    := {| puinst := []; pparams := par_terms; pcontext := [anon_b]; preturn := new_type |} in
  let old_ci      := {| ci_ind := case_ind; ci_npar := n_par; ci_relevance := Relevant |} in
  let inner_branches :=
    mapi (fun ctor_idx ctor =>
      let n_args := ctor.(cstr_arity) in
      let lifted_snoc :=
        List.map (fun snoc_i =>
          let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                       | Some d => d.(decl_type) | None => tVar "?" end in
          match lift_arg_class old_kn n_args snoc_i all_map app_kn_map arg_t with
          | Some None =>
            tApp (tRel (fix_size + n_args + 2 - fix_idx)) [tRel n_args; tRel snoc_i]
          | Some (Some kn) =>
            let fn_ref :=
              match find (fun p => eq_kername (fst p) kn) kn_to_fix_idx with
              | Some (_, k) => tRel (fix_size + n_args + 2 - k)
              | None => tConst (cur_mp, snd kn ++ "Lift") []
              end in
            if existsb (eq_kername kn) npi_set
            then tApp fn_ref [tRel n_args; tRel snoc_i]
            else tApp fn_ref [tRel snoc_i]
          | None => tRel snoc_i
          end)
        (seq 0 n_args) in
      let lifted_args := List.rev lifted_snoc in
      let bbody := match lifted_args with
                   | [] => tConstruct new_ind ctor_idx []
                   | _  => tApp (tConstruct new_ind ctor_idx []) lifted_args
                   end in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    oib.(ind_ctors) in
  let o_branch :=
    {| bcontext := [];
       bbody    := tApp (tConstruct new_ind lift_cstr_idx []) [tRel 0] |} in
  let s_branch :=
    {| bcontext := [anon_b];
       bbody    := tCase old_ci old_pred (tRel 1) inner_branches |} in
  let dbody :=
    tLambda anon_b (tInd nat_ind_ref [])
      (tLambda anon_b old_type
        (tCase nat_ci nat_pred (tRel 1) [o_branch; s_branch])) in
  {| dname := {| binder_name := nNamed (snd old_kn ++ "Lift");
                 binder_relevance := Relevant |};
     dtype  := tProd anon_b (tInd nat_ind_ref []) (tProd anon_b old_type new_type);
     dbody  := dbody;
     rarg   := 0 |}.

(** Build the [def term] entry for one lift function, quoting as needed. *)
Polymorphic Fixpoint collect_lift_defs
    (todo          : list (nat * kername * inductive))
    (all_map       : list (kername * inductive))
    (app_kn_map    : list (kername * list term * inductive))
    (cur_mp        : modpath)
    (sigma2        : bool)
    (npi_set       : list kername)
    (fix_size      : nat)
    (kn_to_fix_idx : list (kername * nat))
    : TemplateMonad (list (def term)) :=
  match todo with
  | [] => tmReturn []
  | (fix_idx, old_kn, new_ind) :: rest =>
    let orig_form :=
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 app_kn_map with
      | Some e => Some (fst (fst e), snd (fst e))
      | None   => None
      end in
    tmBind (tmQuoteInductive old_kn) (fun old_mind =>
    tmBind (
      match nth_error old_mind.(ind_bodies) 0 with
      | None => tmFail ("collect_lift_defs: no body for " ++ snd old_kn)
      | Some oib =>
        if andb sigma2 (existsb (eq_kername old_kn) npi_set) then
          tmBind (tmQuoteInductive (inductive_mind new_ind)) (fun new_mind =>
          let lift_cstr_idx :=
            match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
            | Some new_oib => List.length new_oib.(ind_ctors) - 1
            | None         => 0
            end in
          tmReturn (make_lift_def_sigma2 old_kn oib new_ind all_map app_kn_map
                      cur_mp orig_form npi_set lift_cstr_idx fix_size fix_idx kn_to_fix_idx))
        else
          tmReturn (make_lift_def old_kn oib new_ind all_map app_kn_map cur_mp orig_form
                      fix_size fix_idx kn_to_fix_idx)
      end) (fun d =>
    tmBind (collect_lift_defs rest all_map app_kn_map cur_mp sigma2 npi_set fix_size kn_to_fix_idx)
           (fun rest_defs => tmReturn (d :: rest_defs))))
  end.

(** Declare one lift function per entry as [tFix all_defs fix_idx]. *)
Polymorphic Fixpoint declare_lift_fns
    (todo     : list (kername * inductive))
    (all_defs : list (def term))
    (fix_idx  : nat)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | (old_kn, _) :: rest =>
    fn_term_ev <- tmEval all (tFix all_defs fix_idx) ;;
    tmMkDefinition (snd old_kn ++ "Lift") fn_term_ev ;;
    declare_lift_fns rest all_defs (S fix_idx)
  end.

(** Collect the other lifting-set types that appear as constructor-argument
    types of [old_kn] (looking up via [lift_arg_class]), filtered to those
    in [pi_kns].  Used to determine singleton-tFix declaration order. *)
Definition pi_lift_deps
    (old_kn     : kername)
    (oib        : one_inductive_body)
    (all_map    : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (pi_kns     : list kername)
    : list kername :=
  dedup_kns (flat_map (fun c =>
    let n_args := c.(cstr_arity) in
    flat_map (fun snoc_i =>
      let arg_t := match nth_error c.(cstr_args) snoc_i with
                   | Some d => d.(decl_type) | None => tVar "?" end in
      match lift_arg_class old_kn n_args snoc_i all_map app_kn_map arg_t with
      | Some (Some kn) =>
        if andb (negb (eq_kername kn old_kn)) (existsb (eq_kername kn) pi_kns)
        then [kn] else []
      | _ => []
      end)
    (seq 0 n_args))
  oib.(ind_ctors)).

(** Topological sort of [(kn, ind)] pairs by their [pi_lift_deps] edges.
    A type is emitted only after all types it depends on are emitted.
    Acyclic (pi types have no coinductive transitive deps), so this
    terminates in at most [|entries|] rounds. *)
Fixpoint topo_sort_pi
    (entries : list (kername * inductive * list kername))
    (sorted  : list (kername * inductive))
    (fuel    : nat)
    : list (kername * inductive) :=
  let strip := fun '(kn, ind, _) => (kn, ind) in
  match fuel, entries with
  | 0, _ | _, [] => List.app sorted (List.map strip entries)
  | S f, _ =>
    let sorted_kns := List.map fst sorted in
    let ready := filter (fun '(_, _, deps) =>
                           forallb (fun d => existsb (eq_kername d) sorted_kns) deps)
                        entries in
    let rest  := filter (fun '(_, _, deps) =>
                           negb (forallb (fun d => existsb (eq_kername d) sorted_kns) deps))
                        entries in
    match ready with
    | [] => List.app sorted (List.map strip entries)
    | _  => topo_sort_pi rest (List.app sorted (List.map strip ready)) f
    end
  end.

(** Declare lift functions for pi-sigma2 and arrow types.
    Each is emitted as a standalone singleton [tFix [d] 0] (not mutual).
    Cross-type references use [tConst], so Rocq's guard checker treats each
    function independently and can verify structural termination on its own
    argument.  [todo] must already be in constructor-field dependency order
    (earlier entries referenced by later ones). *)
Polymorphic Fixpoint declare_pi_lift_fns
    (todo       : list (kername * inductive))
    (all_map    : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (cur_mp     : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | (old_kn, new_ind) :: rest =>
    let orig_form :=
      match find (fun e =>
                    andb (eq_kername (inductive_mind (snd e)) (inductive_mind new_ind))
                         (Nat.eqb (inductive_ind (snd e)) (inductive_ind new_ind)))
                 app_kn_map with
      | Some e => Some (fst (fst e), snd (fst e))
      | None   => None
      end in
    old_mind <- tmQuoteInductive old_kn ;;
    match nth_error old_mind.(ind_bodies) 0 with
    | None => declare_pi_lift_fns rest all_map app_kn_map cur_mp
    | Some oib =>
      let d := make_lift_def old_kn oib new_ind all_map app_kn_map cur_mp
                             orig_form 1 0 [] in
      d_ev    <- tmEval all d ;;
      fn_term <- tmEval all (tFix [d_ev] 0) ;;
      tmMkDefinition (snd old_kn ++ "Lift") fn_term ;;
      declare_pi_lift_fns rest all_map app_kn_map cur_mp
    end
  end.

(** Declare lift functions for all types in [todo].
    - Npi sigma2 types ([kn ∈ npi_set]): one mutual [tFix] block where every
      body decreases on [nat] (the depth parameter).  Cross-references between
      npi bodies use [tRel]; cross-references to pi types use [tConst].
    - Pi sigma2 and arrow types: individual singleton [tFix [d] 0] bodies,
      declared in constructor-field dependency order so that each [tConst]
      cross-reference is already in the environment. *)
Polymorphic Definition generate_lift_fns
    (todo       : list (kername * inductive))
    (all_map    : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (cur_mp     : modpath)
    (sigma2     : bool)
    (npi_set    : list kername)
    : TemplateMonad unit :=
  let is_npi kn := andb sigma2 (existsb (eq_kername kn) npi_set) in
  let npi_todo  := filter (fun '(kn, _) => is_npi kn) todo in
  let pi_todo   := filter (fun '(kn, _) => negb (is_npi kn)) todo in
  (* Phase A: npi sigma2 types — mutual tFix, all bodies decrease on nat *)
  (* Phase B: pi sigma2 and arrow types — singleton tFix each, dependency order.
     Pi types are declared BEFORE the npi block because npi lift-function bodies
     may reference pi lift functions via tConst (e.g. coLstLift references tmLift
     when coSeq has a tm arg).  Pi types never reference npi types in their own
     constructor args (compute_npi_step would have marked them npi if they did),
     so declaring pi first is always safe. *)
  let pi_kns := List.map fst pi_todo in
  pi_entries <- monad_map (fun '(old_kn, new_ind) =>
    old_mind <- tmQuoteInductive old_kn ;;
    let deps := match nth_error old_mind.(ind_bodies) 0 with
                | Some oib => pi_lift_deps old_kn oib all_map app_kn_map pi_kns
                | None     => ([] : list kername)
                end in
    tmReturn (old_kn, new_ind, deps)) pi_todo ;;
  pi_entries <- tmEval all pi_entries ;;
  let sorted_pi := topo_sort_pi pi_entries ([] : list (kername * inductive))
                                (S (List.length pi_todo)) in
  declare_pi_lift_fns sorted_pi all_map app_kn_map cur_mp ;;
  (* Phase A: npi sigma2 types — mutual tFix, all bodies decrease on nat.
     Declared after pi so that tConst cross-refs to pi lift fns resolve. *)
  let npi_n := List.length npi_todo in
  let npi_kn_to_fix_idx :=
    snd (fold_left (fun '(i, acc) (entry : kername * inductive) =>
                     (S i, List.app acc [(fst entry, i)]))
                   npi_todo (0, ([] : list (kername * nat)))) in
  let npi_indexed := mapi (fun i '(kn, ind) => (i, kn, ind)) npi_todo in
  npi_defs <- collect_lift_defs npi_indexed all_map app_kn_map cur_mp sigma2 npi_set
                npi_n npi_kn_to_fix_idx ;;
  npi_defs <- tmEval all npi_defs ;;
  declare_lift_fns npi_todo npi_defs 0.

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
    (fn_infos       : list (kername * list term * term))
    (type_map       : list (kername * inductive))
    (app_kn_map     : list (kername * list term * inductive))
    (cur_mp         : modpath)
    (arr_name_pairs : list (term * string))
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
    (* Arrow-type classification: for each arg, check if it matches an arr_name_pairs entry. *)
    let arr_type_infos := List.map (fun tp =>
      find (fun p => rfp_eqb_term (fst p) tp) arr_name_pairs) arg_types in
    let any_arr_input_lifted :=
      existsb (fun o => match o with Some _ => true | None => false end) arr_type_infos in
    let any_input_lifted :=
      orb (existsb (fun o => match o with Some _ => true | None => false end) arg_infos)
          any_arr_input_lifted in
    (* lambda binder types: arrow-type args use fnTypeN, lifted inductives use new_ind, else original *)
    let lifted_arg_types :=
      mapi (fun i pair =>
        match nth i arr_type_infos None with
        | Some (_, nm) => tInd {| inductive_mind := (cur_mp, nm); inductive_ind := 0 |} []
        | None =>
          match fst pair with
          | Some (_, new_ind) => tInd new_ind []
          | None              => snd pair
          end
        end) (combine arg_infos arg_types) in
    (* inside n lambdas, arg i (0-indexed from outermost) = tRel (n-1-i) *)
    let pushed_args :=
      mapi (fun i info =>
        let rel_i := tRel (n - 1 - i) in
        match nth i arr_type_infos None with
        | Some (_, nm) =>
          tApp (tConst (cur_mp, nm ++ "PushPlain") []) [rel_i]
        | None =>
          match info with
          | Some (old_kn, _) =>
            tApp (tConst (cur_mp, snd old_kn ++ "PushPlain") []) [rel_i]
          | None => rel_i
          end
        end) arg_infos in
    let f_applied :=
      match pushed_args with
      | [] => tConst fn_kn []
      | _  => tApp (tConst fn_kn []) pushed_args
      end in
    let chk_terms :=
      flat_map (fun p =>
        let i    := fst p in
        let info := snd p in
        let rel_i := tRel (n - 1 - i) in
        match nth i arr_type_infos None with
        | Some (_, nm) =>
          [tApp (tConst (cur_mp, nm ++ "ChkNoExtraCstrs") []) [rel_i]]
        | None =>
          match info with
          | Some (old_kn, _) =>
            [tApp (tConst (cur_mp, snd old_kn ++ "ChkNoExtraCstrs") []) [rel_i]]
          | None => []
          end
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
           (* When arrow-type args are involved the LiftedCstr constructor in the
              lifted return type has the wrong arg types (still has tProd), so we
              fall back to the zeroth constructor (e.g. Z') to stay type-correct. *)
           let lifted_cstr_out :=
             if any_arr_input_lifted then
               tConstruct new_ret_ind 0 []
             else
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
         (* If the return type is an arrow type, generate_arrow_liftedFuncs
            already declared the correct liftedFunc — skip to avoid duplicate. *)
         if existsb (fun p => rfp_eqb_term (fst p) ret_type) arr_name_pairs
         then tmReturn tt
         else
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
    generate_lifted_fns rest type_map app_kn_map cur_mp arr_name_pairs)
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

(** Like [make_inputLift_term] but for sigma2: adds a leading [depth : nat]
    parameter and passes it to lift functions of non-pi types (kn in [npi_set]).
    De Bruijn depth variable inside the innermost context: [tRel (2 * n_in)].
    This holds because the Success branch adds 1 binder plus build_nested_cases
    adds 2*(n_in-1) binders, totalling 2*n_in-1 new binders; with the extra
    depth lambda outside, depth is at tRel (2*n_in-1 + 1) = tRel (2*n_in). *)
Definition make_inputLift_term_sigma2
    (prod_kn         : kername)
    (anim_res_kn     : kername)
    (in_types        : list term)
    (lifted_types    : list term)
    (lift_fns        : list (option term))
    (lift_needs_depth : list bool)
    : term :=
  let anim_res_ind  := {| inductive_mind := anim_res_kn; inductive_ind := 0 |} in
  let anon_b        := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let nat_ind_ref   := {| inductive_mind := <?nat?>; inductive_ind := 0 |} in
  let in_type       := match in_types     with [t] => t | _ => make_prod_type prod_kn in_types     end in
  let lifted_type   := match lifted_types with [t] => t | _ => make_prod_type prod_kn lifted_types end in
  let anim_in_type  := tApp (tInd anim_res_ind []) [in_type] in
  let anim_out_type := tApp (tInd anim_res_ind []) [lifted_type] in
  let n_in          := List.length in_types in
  let no_match_body := tApp (tConstruct anim_res_ind 2 []) [lifted_type] in
  (* depth_var inside innermost context: tRel (2 * n_in). *)
  let depth_var := tRel (2 * n_in) in
  let lifted_vals :=
    mapi (fun i lf =>
      let needs_d := nth i lift_needs_depth false in
      match lf with
      | Some fn =>
        if needs_d
        then tApp fn [depth_var; input_var i n_in]
        else tApp fn [input_var i n_in]
      | None => input_var i n_in
      end)
    lift_fns in
  let lifted_val    := build_pair_term prod_kn lifted_types lifted_vals in
  let success_inner := tApp (tConstruct anim_res_ind 1 []) [lifted_type; lifted_val] in
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
      [ {| bcontext := []; bbody := no_match_body |}
      ; {| bcontext := [anon_b]; bbody := success_body |}
      ; {| bcontext := []; bbody := no_match_body |} ]
  in
  (* fun (depth : nat) (inp : animation_result in_type) => case_expr *)
  tLambda anon_b (tInd nat_ind_ref [])
    (tLambda anon_b anim_in_type case_expr).

(** Declare [<rel_name>inputLift] for every entry in [kn_mode_list].
    When [sigma2 = true], uses [make_inputLift_term_sigma2]: the generated
    function takes [depth : nat] as its first argument and passes it to
    lift functions of non-pi types (those in [npi_set]). *)
Polymorphic Fixpoint generate_inputLift_fns
    (todo           : list (inductive * (string * (list nat * list nat))))
    (type_map       : list (kername * inductive))
    (app_kn_map     : list (kername * list term * inductive))
    (prod_kn        : kername)
    (anim_res_kn    : kername)
    (cur_mp         : modpath)
    (sigma2         : bool)
    (npi_set        : list kername)
    (arr_name_pairs : list (term * string))
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
      (* Override entries for arrow types: replace (t, None) with (fnTypeN, Some fnTypeNLift). *)
      let classified :=
        mapi (fun i '(lifted_t, lf) =>
          match lf with
          | Some _ => (lifted_t, lf)
          | None =>
            let orig_t := nth i in_types (tVar "?") in
            match find (fun p => rfp_eqb_term (fst p) orig_t) arr_name_pairs with
            | Some (_, nm) =>
              (tInd {| inductive_mind := (cur_mp, nm); inductive_ind := 0 |} [],
               Some (tConst (cur_mp, nm ++ "Lift") []))
            | None => (lifted_t, lf)
            end
          end) classified in
      let lifted_types := List.map fst classified in
      let lift_fns     := List.map snd classified in
      let fn_term :=
        if sigma2 then
          let lift_needs_depth :=
            List.map (fun t =>
              match t with
              | tInd ind _ => existsb (eq_kername (inductive_mind ind)) npi_set
              | tApp (tInd ind _) _ => existsb (eq_kername (inductive_mind ind)) npi_set
              | _ => false
              end)
            in_types in
          make_inputLift_term_sigma2 prod_kn anim_res_kn in_types lifted_types
                                     lift_fns lift_needs_depth
        else
          make_inputLift_term prod_kn anim_res_kn in_types lifted_types lift_fns in
      fn_term_ev <- tmEval all fn_term ;;
      tmBind (tmMkDefinition (rel_name ++ "inputLift") fn_term_ev) (fun _ =>
      generate_inputLift_fns rest type_map app_kn_map prod_kn anim_res_kn cur_mp sigma2 npi_set arr_name_pairs)
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
    lift_relation (inductive_mind rel_ind) [] type_mapping [] modes [] [] false
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
    preproc_result <- preprocess_coind_types modes fuel false ;;
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
    _ <- generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp false [] ;;
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
      _ <- generate_lifted_fns unique_fn_infos type_mapping app_kn_mapping cur_mp [] ;;
      (* Build fn_kn_map from unique_fn_infos: every function that has a liftedFunc
         definition maps old_kn → (cur_mp, name ++ "liftedFunc"). *)
      let fn_kn_map :=
        List.map (fun fi => (fst (fst fi), (cur_mp, snd (fst (fst fi)) ++ "liftedFunc")))
                 unique_fn_infos in
      (* Now all liftedFunc constants exist; declare the lifted relation blocks. *)
      _ <- monad_fold_left (fun _ block_kn =>
        let block_modes :=
          List.map snd (filter (fun p => eq_kername (inductive_mind (fst p)) block_kn) kn_mode_list) in
        lift_relation block_kn rel_mapping type_mapping app_kn_mapping block_modes fn_kn_map [] false)
        sorted_block_kns tt ;;
      _ <- generate_inputLift_fns kn_mode_list type_mapping app_kn_mapping
                                   prod_kn anim_res_kn cur_mp false [] [] ;;
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

(** True if [suf] is a suffix of [s] (bytestring version). *)
Fixpoint string_is_suffix (s suf : string) : bool :=
  if String.eqb s suf then true
  else match s with
       | String.EmptyString => false
       | String.String _ r  => string_is_suffix r suf
       end.

(** Return the first [n] characters of [s] (bytestring version). *)
Fixpoint string_take (n : nat) (s : string) : string :=
  match n, s with
  | 0, _                   => String.EmptyString
  | _, String.EmptyString  => String.EmptyString
  | S n', String.String c r => String.String c (string_take n' r)
  end.

(** Length of a bytestring. *)
Fixpoint string_len (s : string) : nat :=
  match s with
  | String.EmptyString   => 0
  | String.String _ rest => S (string_len rest)
  end.

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
    (sigma2      : bool)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | entry :: rest =>
    let old_kn  := fst entry in
    let new_ind := snd entry in
    let type_nm := snd old_kn in
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
              (* sigma2: skip the LiftCstr constructor — it has no animation hole. *)
              let extra := if sigma2
                           then filter (fun c => negb (String.eqb c.(cstr_name) (type_nm ++ "LiftCstr"))) extra
                           else extra in
              (* LiftedCstr constructors represent function applications and get replaced
                 by the concrete function during pushing — no Symb hole needed. *)
              let extra := filter (fun c => negb (string_is_suffix c.(cstr_name) "LiftedCstr")) extra in
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
    generate_fnSymb_wrapper_inductives rest type_map app_kn_map cur_mp sigma2)))
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
    (old_kn         : kername)
    (new_ind        : inductive)
    (n_block        : nat)
    (new_oib        : one_inductive_body)
    (n_old_ctors    : nat)
    (type_map       : list (kername * inductive))
    (pi_set         : list kername)
    (is_purely_ind  : bool)
    (is_sigma2      : bool)
    (cur_mp         : modpath)
    (pi_set_holes   : list (kername * list term))
    (arr_name_pairs : list (term * string))
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
      (* sigma2: LiftCstr embeds an old value — no animation hole needed. *)
      else if andb is_sigma2 (String.eqb ctor.(cstr_name) (type_nm ++ "LiftCstr")) then []
      (* LiftedCstr: function application constructor — no hole, concrete fn used at push. *)
      else if string_is_suffix ctor.(cstr_name) "LiftedCstr" then []
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
        | _ =>
          (* Also pull in holes from lifted arrow-type args. *)
          match arg_t with
          | tInd ind _ =>
            let arg_kn := inductive_mind ind in
            match find (fun e => eq_kername (cur_mp, snd e) arg_kn) arr_name_pairs with
            | Some (_, arr_nm) =>
              match find (fun e => eq_kername (fst e) (cur_mp, arr_nm)) pi_set_holes with
              | Some (_, kn_hs) => kn_hs
              | None => []
              end
            | None => []
            end
          | _ => []
          end
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
    (is_sigma2       : bool)
    (fn_name_kn_map  : list (string * kername))
    (arr_name_pairs  : list (term * string))
    : def term :=
  (* sigma2: all lifted types are inductive, structural recursion on s for all types. *)
  let is_purely_ind := orb is_purely_ind is_sigma2 in
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
              | None =>
                match arg_t with
                | tInd ind _ =>
                  let arg_kn := inductive_mind ind in
                  match find (fun e => eq_kername (cur_mp, snd e) arg_kn) arr_name_pairs with
                  | Some (_, arr_nm) =>
                    let arr_kn := (cur_mp, arr_nm) in
                    let kn_h_refs : list term := kn_hole_refs_in_s n_args arr_kn in
                    tApp (tConst (cur_mp, arr_nm ++ "TransparentSigmaPushBody") [])
                         (List.app kn_h_refs [tRel snoc_i])
                  | None => tRel snoc_i
                  end
                | _ => tRel snoc_i
                end
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
          (* Extra constructor dispatch:
             (a) sigma2 LiftCstr: embeds old value directly — return tRel 0.
             (b) LiftedCstr: function application constructor — apply the concrete
                 original function (no hole) to the pushed args.
             (c) An constructor (animation hole): apply Symb_unwrap hole. *)
          let ctor_nm  := ctor.(cstr_name) in
          if andb is_sigma2 (String.eqb ctor_nm (type_nm ++ "LiftCstr")) then tRel 0
          else
          let is_lifted_cstr := string_is_suffix ctor_nm "LiftedCstr" in
          let push_arg_term := fun snoc_i =>
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
            | None =>
              match arg_t with
              | tInd ind _ =>
                let arg_kn := inductive_mind ind in
                match find (fun e => eq_kername (cur_mp, snd e) arg_kn) arr_name_pairs with
                | Some (_, arr_nm) =>
                  let arr_kn := (cur_mp, arr_nm) in
                  let kn_h_refs : list term := kn_hole_refs_in_s n_args arr_kn in
                  tApp (tConst (cur_mp, arr_nm ++ "TransparentSigmaPushBody") [])
                       (List.app kn_h_refs [tRel snoc_i])
                | None => tRel snoc_i
                end
              | _ => tRel snoc_i
              end
            end in
          let pushed_snoc := List.map push_arg_term (seq 0 n_args) in
          let pushed := List.rev pushed_snoc in
          if is_lifted_cstr then
            (* Strip "LiftedCstr" suffix (10 chars) to recover original function name. *)
            let fn_nm  := string_take (string_len ctor_nm - 10) ctor_nm in
            let fn_kn  := match find (fun p => String.eqb (fst p) fn_nm) fn_name_kn_map with
                          | Some (_, kn) => kn
                          | None         => (cur_mp, fn_nm)
                          end in
            let fn_ref := tConst fn_kn [] in
            match pushed with
            | [] => fn_ref
            | _  => tApp fn_ref pushed
            end
          else
          let w_kn   := (cur_mp, ctor_nm ++ "Symb") in
          let w_idx  := find_hole_idx_by_kn w_kn unique_ht_terms in
          let fn_ref := tApp (tConst (cur_mp, ctor_nm ++ "Symb_unwrap") [])
                             [s_hole_ref n_args w_idx] in
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
    (is_sigma2      : bool)
    (fn_name_kn_map : list (string * kername))
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
    let n_old_ctors :=
      match nth_error old_mind.(ind_bodies) 0 with
      | Some ob => List.length ob.(ind_ctors) | None => 0
      end in
    let n_block       := List.length new_mind.(ind_bodies) in
    (* sigma2: treat all types as purely inductive for the push (LiftCstr provides the embedding). *)
    let is_purely_ind := orb (existsb (eq_kername old_kn) pi_set) is_sigma2 in
    let '(unique_ht_terms, _) :=
      match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
      | Some new_oib =>
        compute_push_unique_holes old_kn new_ind n_block new_oib n_old_ctors
          all_map pi_set is_purely_ind is_sigma2 cur_mp pi_set_holes []
      | None => ([], [])
      end in
    tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
            | None =>
              tmFail ("generate_transparent_sigma_push_fns: no body for " ++ snd old_kn)
            | Some new_oib =>
              let d_body := make_transparent_sigma_push_body_def
                              old_kn new_ind n_block new_oib n_old_ctors
                              all_map app_kn_map pi_set is_purely_ind cur_mp
                              unique_ht_terms pi_set_holes is_sigma2 fn_name_kn_map [] in
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
        (pi_set_holes ++ [(old_kn, unique_ht_terms)]) is_sigma2 fn_name_kn_map)
  end.

(** Classify an output type for the transparent-sigma output push:
    uses [typeNmTransparentSigmaPush] (returns [HoleyResult T] with named holes). *)
Definition classify_out_type_transparent_sigma
    (type_map       : list (kername * inductive))
    (app_kn_map     : list (kername * list term * inductive))
    (pi_set         : list kername)
    (arr_name_pairs : list (term * string))
    (cur_mp         : modpath)
    (t              : term)
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
  | _ =>
    (* Arrow type: look up in arr_name_pairs for fnTypeN-lifted output types. *)
    match find (fun '(arr_t, _) => rfp_eqb_term arr_t t) arr_name_pairs with
    | Some (_, nm) =>
      let ind_ref := {| inductive_mind := (cur_mp, nm); inductive_ind := 0 |} in
      (tInd ind_ref [], Some (tConst (cur_mp, nm ++ "TransparentSigmaPush") [], true))
    | None => (t, None)
    end
  end.

(** Declare [relTransparentSigmaOutputPush] for every entry in [kn_mode_list]. *)
Polymorphic Fixpoint generate_transparent_sigma_outputPush_fns
    (todo           : list (inductive * (string * (list nat * list nat))))
    (type_map       : list (kername * inductive))
    (app_kn_map     : list (kername * list term * inductive))
    (pi_set         : list kername)
    (arr_name_pairs : list (term * string))
    (prod_kn        : kername)
    (anim_res_kn    : kername)
    (cur_mp         : modpath)
    (hr_type_c      : term)
    (hr_pair_c      : term)
    (hr_pure_c      : term)
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
        List.map (classify_out_type_transparent_sigma type_map app_kn_map pi_set arr_name_pairs cur_mp)
                 orig_types in
      let lifted_types := List.map fst classified in
      let push_fns     := List.map snd classified in
      let fn_term := make_outputPush_term prod_kn anim_res_kn orig_types lifted_types push_fns
                                          hr_type_c hr_pair_c hr_pure_c in
      fn_term_ev <- tmEval all fn_term ;;
      tmBind (tmMkDefinition (rel_name ++ "TransparentSigmaOutputPush") fn_term_ev) (fun _ =>
      generate_transparent_sigma_outputPush_fns rest type_map app_kn_map pi_set arr_name_pairs
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
    (rel_nm              : ident)
    (type_minds          : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (type_map            : list (kername * inductive))
    (app_kn_map          : list (kername * list term * inductive))
    (pi_set              : list kername)
    (cur_mp              : modpath)
    (kn_mode_list        : list (inductive * (string * (list nat * list nat))))
    (fn_infos            : list (kername * list term * term))
    (sigma2              : bool)
    (extra_an_hole_infos : list (inductive * inductive * string * term))
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
  let an_hole_infos      := List.app extra_an_hole_infos
                              (collect_an_hole_infos type_minds type_map app_kn_map kn_mode_list) in
  let push_hole_infos    := if sigma2 then [] else collect_coind_push_hole_infos type_minds pi_set in
  let pi_push_hole_infos := if sigma2 then [] else collect_pi_push_hole_infos type_minds pi_set in
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
    preproc_result <- preprocess_coind_types modes fuel false ;;
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
    _ <- generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp false [] ;;
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
      _ <- generate_lifted_fns unique_fn_infos type_mapping app_kn_mapping cur_mp [] ;;
      let fn_kn_map :=
        List.map (fun fi => (fst (fst fi), (cur_mp, snd (fst (fst fi)) ++ "liftedFunc")))
                 unique_fn_infos in
      _ <- monad_fold_left (fun _ block_kn =>
        let block_modes :=
          List.map snd (filter (fun p => eq_kername (inductive_mind (fst p)) block_kn) kn_mode_list) in
        lift_relation block_kn rel_mapping type_mapping app_kn_mapping block_modes fn_kn_map [] false)
        sorted_block_kns tt ;;
      _ <- generate_inputLift_fns kn_mode_list type_mapping app_kn_mapping
                                   prod_kn anim_res_kn cur_mp false [] [] ;;
      _ <- generate_rest_fns kn_mode_list cur_mp prod_kn ;;
      (* Generate fnSymb wrapper inductives (ctorNameSymb for animation ctor holes). *)
      _ <- generate_fnSymb_wrapper_inductives type_mapping type_mapping app_kn_mapping cur_mp false ;;
      (* Generate wrapper inductives for push holes: coIndPushSymb (non-pi) and PushFullSymb (pi). *)
      _ <- generate_pushSymb_wrapper_inductives type_minds type_mapping app_kn_mapping
                                                pi_set cur_mp "coIndPushSymb" false ;;
      _ <- generate_pushSymb_wrapper_inductives type_minds type_mapping app_kn_mapping
                                                pi_set cur_mp "PushFullSymb" true ;;
      (* Transparent sigma push functions: body takes hole values, wrapper holds static hole list.
         Sort so pi-set types (whose bodies reference no other bodies) come first. *)
      let fn_name_kn_map :=
        List.map (fun fi => (snd (fst (fst fi)), fst (fst fi))) unique_fn_infos in
      let type_minds_pi_first :=
        List.app
          (List.filter (fun '((old_kn, _), _) => existsb (eq_kername old_kn) pi_set) type_minds)
          (List.filter (fun '((old_kn, _), _) => negb (existsb (eq_kername old_kn) pi_set)) type_minds) in
      _ <- generate_transparent_sigma_push_fns type_minds_pi_first type_mapping app_kn_mapping pi_set cur_mp
                      hr_hole_tm hr_pure_tm hr_ap_tm hr_map_tm hr_type_tm [] false fn_name_kn_map ;;
      (* Output push for the transparent sigma version. *)
      _ <- generate_transparent_sigma_outputPush_fns kn_mode_list type_mapping app_kn_mapping pi_set []
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
                  kn_mode_list unique_fn_infos false [] ;;
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

(** Like [animate_coinductive_transparent_sigma] but with two modifications:
    1. All lifted types and lifted relations are declared as [Inductive] (Finite),
       regardless of whether the originals were coinductive.
    2. Each non-pi lifted type gains an extra constructor
       [typeNameLiftCstr : original_type -> lifted_type],
       which embeds an already-computed original value directly into the lifted type.
       The push function for [LiftCstr] is [hr_pure s] (identity, no holes needed).
    Because all lifted types are finite, structural recursion on the lifted type
    always terminates; the depth/fuel parameter used in sigma1 for coinductive types
    is eliminated for all types. *)
Unset Universe Checking.
Polymorphic Definition animate_coinductive_transparent_sigma2
    (rel_kn : kername)
    (modes  : mode_map)
    (fuel   : nat)
    : TemplateMonad unit :=
  let rel_nm := snd rel_kn in
  kn_mode_list <- monad_fold_left (fun acc me =>
    refs <- tmLocate (fst me) ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [(ind, me)])
    | _ => tmFail ("animate_coinductive_transparent_sigma2: cannot find '" ++ fst me ++ "'")
    end)
    modes [] ;;
  match kn_mode_list return TemplateMonad unit with
  | [] => @tmFail unit "animate_coinductive_transparent_sigma2: no modes provided"
  | _  =>
    (* sigma2 = true: force all lifted types Finite, add LiftCstr constructors. *)
    preproc_result <- preprocess_coind_types modes fuel true ;;
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
    (* Compute npi_set early so sigma2 lift functions can pass depth to non-pi calls. *)
    npi_set_lift <- compute_npi_fix type_mapping [] (List.length type_mapping + 1) ;;
    npi_set_lift <- tmEval all npi_set_lift ;;
    _ <- generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp true npi_set_lift ;;
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
      _ <- generate_lifted_fns unique_fn_infos type_mapping app_kn_mapping cur_mp [] ;;
      let fn_kn_map :=
        List.map (fun fi => (fst (fst fi), (cur_mp, snd (fst (fst fi)) ++ "liftedFunc")))
                 unique_fn_infos in
      _ <- monad_fold_left (fun _ block_kn =>
        let block_modes :=
          List.map snd (filter (fun p => eq_kername (inductive_mind (fst p)) block_kn) kn_mode_list) in
        (* sigma2: force lifted relation to be Finite (inductive). *)
        lift_relation block_kn rel_mapping type_mapping app_kn_mapping block_modes fn_kn_map [] true)
        sorted_block_kns tt ;;
      _ <- generate_inputLift_fns kn_mode_list type_mapping app_kn_mapping
                                   prod_kn anim_res_kn cur_mp true npi_set [] ;;
      _ <- generate_rest_fns kn_mode_list cur_mp prod_kn ;;
      _ <- generate_fnSymb_wrapper_inductives type_mapping type_mapping app_kn_mapping cur_mp true ;;
      _ <- generate_pushSymb_wrapper_inductives type_minds type_mapping app_kn_mapping
                                                pi_set cur_mp "coIndPushSymb" false ;;
      _ <- generate_pushSymb_wrapper_inductives type_minds type_mapping app_kn_mapping
                                                pi_set cur_mp "PushFullSymb" true ;;
      (* sigma2: all types treated as pi; LiftCstr branch handles embedded values. *)
      let fn_name_kn_map :=
        List.map (fun fi => (snd (fst (fst fi)), fst (fst fi))) unique_fn_infos in
      _ <- generate_transparent_sigma_push_fns type_minds type_mapping app_kn_mapping pi_set cur_mp
                      hr_hole_tm hr_pure_tm hr_ap_tm hr_map_tm hr_type_tm [] true fn_name_kn_map ;;
      (* sigma2: all push fns are pi-style (no depth), pass full type_mapping as pi_set. *)
      let pi_set_all := List.map fst type_mapping in
      _ <- generate_transparent_sigma_outputPush_fns kn_mode_list type_mapping app_kn_mapping pi_set_all []
                              prod_kn anim_res_kn cur_mp hr_type_tm hr_pair_tm hr_pure_tm ;;
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
          (* inputLift takes (depth inp) in sigma2; pass fuel = tRel 1. *)
          let composite :=
            tLambda anon_b (tInd nat_ind [])
            (tLambda anon_b anim_in_type
            (tApp transparentSigmaPush_fn
              [tRel 1;
               tApp animFn [tRel 1; tApp inputLift_fn [tRel 1; tRel 0]]]))
          in
          _ <- generate_animated_top_fn_prop
                  rel_nm type_minds type_mapping app_kn_mapping pi_set cur_mp
                  kn_mode_list unique_fn_infos true [] ;;
          tmMkDefinition (rel_nm ++ "TransparentSigma2AnimatedTopFn") composite
        | _, _ =>
          tmFail "animate_coinductive_transparent_sigma2: cannot locate prod or animation_result (2)"
        end
      | None, _ => tmFail ("animate_coinductive_transparent_sigma2: no mode entry for " ++ rel_nm)
      | _, None  => tmFail ("animate_coinductive_transparent_sigma2: cannot find body " ++ rel_nm)
      end
    | _, _ => @tmFail unit "animate_coinductive_transparent_sigma2: cannot locate prod or animation_result"
    end
  end.
Set Universe Checking.

(* ================================================================== *)
(** ** remove_from_fn_pos                                              *)
(**   Scan relation constructors for anonymous closed lambdas and      *)
(**   locally-bound variable function applications (tApp (tRel i) …). *)
(**   For each unique pattern declare a named wrapper (fnApp_N /        *)
(**   fnLam_N) and re-declare every relation as old_name++removeFnPos. *)
(**   All traversals use pure structural recursion on [term] — no fuel *)
(**   parameter is needed or accepted.                                 *)
(* ================================================================== *)

(** True iff no free de Bruijn variable appears with index >= n. *)
Fixpoint rfp_is_closed_under (n : nat) (t : term) : bool :=
  match t with
  | tRel i               => Nat.ltb i n
  | tVar _ | tSort _ | tConst _ _ | tInd _ _ | tConstruct _ _ _ => true
  | tProd _ ty body
  | tLambda _ ty body    => andb (rfp_is_closed_under n ty)
                                 (rfp_is_closed_under (S n) body)
  | tLetIn _ v ty body   => andb (rfp_is_closed_under n v)
                            (andb (rfp_is_closed_under n ty)
                                  (rfp_is_closed_under (S n) body))
  | tApp f args          => andb (rfp_is_closed_under n f)
                                 (forallb (rfp_is_closed_under n) args)
  | tCast c _ v          => andb (rfp_is_closed_under n c)
                                 (rfp_is_closed_under n v)
  | tCase _ pred disc brs =>
    andb (forallb (rfp_is_closed_under n) pred.(pparams))
    (andb (rfp_is_closed_under n disc)
          (forallb (fun br =>
            rfp_is_closed_under (n + #|br.(bcontext)|) br.(bbody)) brs))
  | tFix mfix _ | tCoFix mfix _ =>
    forallb (fun d =>
      andb (rfp_is_closed_under (n + #|mfix|) d.(dtype))
           (rfp_is_closed_under (n + #|mfix|) d.(dbody))) mfix
  | tEvar _ args         => forallb (rfp_is_closed_under n) args
  | _                    => true
  end.

Fixpoint rfp_decompose_arrows (t : term) : list term * term :=
  match t with
  | tProd _ ty body =>
    let '(args, ret) := rfp_decompose_arrows body in
    (ty :: args, ret)
  | _ => ([], t)
  end.

(** Two var-app signatures agree if they have the same fn_type and arity. *)
Definition rfp_eqb_sig (s1 s2 : term * list term * term) : bool :=
  let '(ft1, ats1, _) := s1 in
  let '(ft2, ats2, _) := s2 in
  andb (rfp_eqb_term ft1 ft2) (Nat.eqb #|ats1| #|ats2|).

(** Build [fun (f:fn_type)(a1:at1)...(an:atn) => f a1 ... an].
    All types must be closed. *)
Definition rfp_build_fnapp_body (fn_type : term) (arg_types : list term) : term :=
  let anon := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let n    := List.length arg_types in
  let inner :=
    match arg_types with
    | [] => tRel 0
    | _  => tApp (tRel n) (List.rev (mapi (fun i _ => tRel i) arg_types))
    end in
  List.fold_right (fun ty acc => tLambda anon ty acc) inner (fn_type :: arg_types).

(** Scan [t] under de Bruijn context [ctx].
    Returns (var_app_sigs, closed_lams).
    Structurally recursive on [t]. *)
Fixpoint rfp_scan (ctx : list term) (t : term)
    : list (term * list term * term) * list term :=
  let sc  := rfp_scan ctx in
  let sc1 ty := rfp_scan (ty :: ctx) in
  match t with
  | tProd _ ty body =>
    let r1 := sc  ty   in
    let r2 := sc1 ty body in
    (List.app (fst r1) (fst r2), List.app (snd r1) (snd r2))
  | tLambda b ty body =>
    let lam_term := tLambda b ty body in
    if rfp_is_closed_under 0 lam_term then
      ([], [lam_term])
    else
      let r1 := sc  ty   in
      let r2 := sc1 ty body in
      (List.app (fst r1) (fst r2),
       List.app (snd r1) (snd r2))
  | tLetIn _ v ty body =>
    let r1 := sc ty   in
    let r2 := sc v    in
    let r3 := sc1 ty body in
    (List.app (fst r1) (List.app (fst r2) (fst r3)),
     List.app (snd r1) (List.app (snd r2) (snd r3)))
  | tApp f args =>
    let rf      := sc f in
    let va_args := flat_map (fun a => fst (sc a)) args in
    let la_args := flat_map (fun a => snd (sc a)) args in
    let var_hit :=
      match f with
      | tRel i =>
        match nth_error ctx i with
        | Some fn_type =>
          if rfp_is_closed_under 0 fn_type then
            let '(arg_types, ret_type) := rfp_decompose_arrows fn_type in
            if Nat.eqb (List.length args) (List.length arg_types) then
              [(fn_type, arg_types, ret_type)]
            else []
          else []
        | None => []
        end
      | _ => []
      end in
    (List.app var_hit (List.app (fst rf) va_args),
     List.app (snd rf) la_args)
  | _ => ([], [])
  end.

(** Scan all argument types of a constructor (outer-to-inner order). *)
Definition rfp_scan_cstr (c : constructor_body)
    : list (term * list term * term) * list term :=
  let '(vas, lams, full_ctx) :=
    fold_left (fun '(va, la, ctx) d =>
      let r := rfp_scan ctx d.(decl_type) in
      (List.app va (fst r), List.app la (snd r), d.(decl_type) :: ctx))
    (List.rev c.(cstr_args)) ([], [], []) in
  (* Also scan the conclusion indices — they share the same de Bruijn context
     as the innermost argument (full_ctx built from all cstr_args). *)
  let idx_results := List.map (rfp_scan full_ctx) c.(cstr_indices) in
  let idx_vas  := flat_map fst idx_results in
  let idx_lams := flat_map snd idx_results in
  (List.app vas idx_vas, List.app lams idx_lams).

(** Rename tInd block kernames via [mapping], preserving inductive_ind. *)
Fixpoint rfp_subst_ind_kns (mapping : list (kername * kername)) (t : term) : term :=
  let rn kn :=
    match find (fun p => eq_kername (fst p) kn) mapping with
    | Some (_, kn') => kn'
    | None          => kn
    end in
  match t with
  | tInd ind ui     => tInd {| inductive_mind := rn (inductive_mind ind)
                              ; inductive_ind  := inductive_ind ind |} ui
  | tEvar ev args   => tEvar ev (List.map (rfp_subst_ind_kns mapping) args)
  | tCast c k v     => tCast (rfp_subst_ind_kns mapping c) k
                             (rfp_subst_ind_kns mapping v)
  | tProd na ty b   => tProd na (rfp_subst_ind_kns mapping ty)
                               (rfp_subst_ind_kns mapping b)
  | tLambda na ty b => tLambda na (rfp_subst_ind_kns mapping ty)
                                  (rfp_subst_ind_kns mapping b)
  | tLetIn na v ty b => tLetIn na (rfp_subst_ind_kns mapping v)
                                   (rfp_subst_ind_kns mapping ty)
                                   (rfp_subst_ind_kns mapping b)
  | tApp f args     => tApp (rfp_subst_ind_kns mapping f)
                            (List.map (rfp_subst_ind_kns mapping) args)
  | tCase ci pred disc brs =>
    tCase ci
      {| pparams  := List.map (rfp_subst_ind_kns mapping) pred.(pparams)
       ; puinst   := pred.(puinst)
       ; pcontext := pred.(pcontext)
       ; preturn  := rfp_subst_ind_kns mapping pred.(preturn) |}
      (rfp_subst_ind_kns mapping disc)
      (List.map (fun br =>
        {| bcontext := br.(bcontext)
         ; bbody    := rfp_subst_ind_kns mapping br.(bbody) |}) brs)
  | tProj p c       => tProj p (rfp_subst_ind_kns mapping c)
  | _               => t
  end.

(** Apply all substitutions to [t] under de Bruijn context [ctx].
    Structurally recursive on [t]:
    - kn_rename:  rename tInd block kernames
    - sig_to_kn:  (fn_type, arg_types, wrapper_kn) replace var-app
    - lam_to_kn:  (lam_term, wrapper_kn) replace closed lambda *)
Fixpoint rfp_substitute (ctx : list term)
    (kn_rename : list (kername * kername))
    (sig_to_kn : list (term * list term * kername))
    (lam_to_kn : list (term * kername))
    (t : term) : term :=
  let sub     := rfp_substitute ctx kn_rename sig_to_kn lam_to_kn in
  let sub_ext ty := rfp_substitute (ty :: ctx) kn_rename sig_to_kn lam_to_kn in
  match t with
  | tInd ind ui =>
    let new_kn :=
      match find (fun p => eq_kername (fst p) (inductive_mind ind)) kn_rename with
      | Some (_, kn') => kn'
      | None          => inductive_mind ind
      end in
    tInd {| inductive_mind := new_kn; inductive_ind := inductive_ind ind |} ui
  | tLambda b ty body =>
    let lam_term := tLambda b ty body in
    if rfp_is_closed_under 0 lam_term then
      match find (fun p => rfp_eqb_term (fst p) lam_term) lam_to_kn with
      | Some (_, kn) => tConst kn []
      | None         => tLambda b (sub ty) (sub_ext ty body)
      end
    else
      tLambda b (sub ty) (sub_ext ty body)
  | tProd b ty body    => tProd b (sub ty) (sub_ext ty body)
  | tLetIn b v ty body => tLetIn b (sub v) (sub ty) (sub_ext ty body)
  | tApp f args =>
    match f with
    | tRel i =>
      match nth_error ctx i with
      | Some fn_type =>
        if rfp_is_closed_under 0 fn_type then
          let '(arg_types, _) := rfp_decompose_arrows fn_type in
          if Nat.eqb (List.length args) (List.length arg_types) then
            match find (fun '(ft, ats, _) =>
                andb (rfp_eqb_term ft fn_type)
                (andb (Nat.eqb #|ats| #|arg_types|)
                      (forallb (fun p => rfp_eqb_term (fst p) (snd p))
                               (combine ats arg_types))))
              sig_to_kn with
            | Some (_, _, wrapper_kn) =>
              tApp (tConst wrapper_kn []) (tRel i :: List.map sub args)
            | None => tApp (sub f) (List.map sub args)
            end
          else tApp (sub f) (List.map sub args)
        else tApp (sub f) (List.map sub args)
      | None => tApp (sub f) (List.map sub args)
      end
    | _ => tApp (sub f) (List.map sub args)
    end
  | tCast c k v  => tCast (sub c) k (sub v)
  | tCase ci pred disc brs =>
    tCase ci
      {| pparams  := List.map sub pred.(pparams)
       ; puinst   := pred.(puinst)
       ; pcontext := pred.(pcontext)
       ; preturn  := sub pred.(preturn) |}
      (sub disc)
      (List.map (fun br =>
        {| bcontext := br.(bcontext)
         ; bbody    := sub br.(bbody) |}) brs)
  | tProj p c => tProj p (sub c)
  | _         => t
  end.

Definition rfp_sub_decl (ctx : list term)
    (kn_rename : list (kername * kername))
    (sig_to_kn : list (term * list term * kername))
    (lam_to_kn : list (term * kername))
    (d : context_decl) : context_decl :=
  let sub t := rfp_substitute ctx kn_rename sig_to_kn lam_to_kn t in
  {| decl_name := d.(decl_name)
   ; decl_body := option_map sub d.(decl_body)
   ; decl_type := sub d.(decl_type) |}.

Definition rfp_transform_cstr
    (kn_rename : list (kername * kername))
    (sig_to_kn : list (term * list term * kername))
    (lam_to_kn : list (term * kername))
    (c : constructor_body) : constructor_body :=
  let '(new_args_rev, full_ctx) :=
    fold_left (fun '(acc, ctx) d =>
      let new_d := rfp_sub_decl ctx kn_rename sig_to_kn lam_to_kn d in
      (new_d :: acc, d.(decl_type) :: ctx))
    (List.rev c.(cstr_args)) ([], []) in
  let new_args := List.rev new_args_rev in
  let sub t := rfp_substitute full_ctx kn_rename sig_to_kn lam_to_kn t in
  {| cstr_name    := c.(cstr_name) ++ "removeFnPos"
   ; cstr_args    := new_args
   ; cstr_indices := List.map sub c.(cstr_indices)
   ; cstr_type    := sub c.(cstr_type)
   ; cstr_arity   := c.(cstr_arity) |}.

Definition rfp_transform_oib
    (kn_rename : list (kername * kername))
    (sig_to_kn : list (term * list term * kername))
    (lam_to_kn : list (term * kername))
    (oib : one_inductive_body) : one_inductive_body :=
  let sub_t t := rfp_substitute [] kn_rename sig_to_kn lam_to_kn t in
  let sub_d d := rfp_sub_decl  [] kn_rename sig_to_kn lam_to_kn d in
  {| ind_name      := oib.(ind_name) ++ "removeFnPos"
   ; ind_indices   := List.map sub_d oib.(ind_indices)
   ; ind_sort      := oib.(ind_sort)
   ; ind_type      := sub_t oib.(ind_type)
   ; ind_kelim     := oib.(ind_kelim)
   ; ind_ctors     := List.map
                        (rfp_transform_cstr kn_rename sig_to_kn lam_to_kn)
                        oib.(ind_ctors)
   ; ind_projs     := oib.(ind_projs)
   ; ind_relevance := oib.(ind_relevance) |}.

(** Transform a full mutual block: rename bodies, substitute references,
    then apply subst_block_inds_to_rels so self-references become tRel
    as required by tmMkInductive. *)
Definition rfp_transform_mind (old_kn : kername) (cur_mp : modpath)
    (kn_rename : list (kername * kername))
    (sig_to_kn : list (term * list term * kername))
    (lam_to_kn : list (term * kername))
    (mind : mutual_inductive_body) : mutual_inductive_body :=
  let n_bodies := #|mind.(ind_bodies)| in
  let new_kn :=
    match find (fun p => eq_kername (fst p) old_kn) kn_rename with
    | Some (_, kn') => kn'
    | None          => (cur_mp, snd old_kn ++ "removeFnPos")
    end in
  let new_bodies :=
    List.map (rfp_transform_oib kn_rename sig_to_kn lam_to_kn)
             mind.(ind_bodies) in
  let s3t t  := subst_block_inds_to_rels new_kn n_bodies 0 t in
  let s3d d  := {| decl_name := d.(decl_name)
                 ; decl_body := d.(decl_body)
                 ; decl_type := s3t d.(decl_type) |} in
  let s3c c  := {| cstr_name    := c.(cstr_name)
                 ; cstr_args    := List.map s3d c.(cstr_args)
                 ; cstr_indices := List.map s3t c.(cstr_indices)
                 ; cstr_type    := s3t c.(cstr_type)
                 ; cstr_arity   := c.(cstr_arity) |} in
  let final_bodies :=
    List.map (fun oib =>
      {| ind_name      := oib.(ind_name)
       ; ind_indices   := List.map s3d oib.(ind_indices)
       ; ind_sort      := oib.(ind_sort)
       ; ind_type      := s3t oib.(ind_type)
       ; ind_kelim     := oib.(ind_kelim)
       ; ind_ctors     := List.map s3c oib.(ind_ctors)
       ; ind_projs     := oib.(ind_projs)
       ; ind_relevance := oib.(ind_relevance) |}) new_bodies in
  {| ind_finite    := mind.(ind_finite)
   ; ind_npars     := mind.(ind_npars)
   ; ind_universes := mind.(ind_universes)
   ; ind_variance  := mind.(ind_variance)
   ; ind_params    := mind.(ind_params)
   ; ind_bodies    := final_bodies |}.

Unset Universe Checking.
Polymorphic Definition remove_from_fn_pos
    (top_kn : kername)
    (modes  : mode_map)
    : TemplateMonad unit :=
  cur_mp <- tmCurrentModPath tt ;;
  (* Resolve each mode entry name to its block kername. *)
  kn_list <- monad_map (fun me =>
    refs <- tmLocate (fst me) ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (inductive_mind ind)
    | _ => tmFail ("remove_from_fn_pos: cannot find '" ++ fst me ++ "'")
    end) modes ;;
  let unique_kns :=
    fold_left (fun acc kn =>
      if existsb (eq_kername kn) acc then acc else List.app acc [kn])
    kn_list [] in
  minds <- monad_map (fun kn => tmQuoteInductive kn) unique_kns ;;
  (* Scan every constructor for var-app and closed-lambda patterns. *)
  let scan_results :=
    flat_map (fun mind =>
      flat_map (fun oib => List.map rfp_scan_cstr oib.(ind_ctors))
               mind.(ind_bodies))
    minds in
  let all_vas  := flat_map fst scan_results in
  let all_lams := flat_map snd scan_results in
  let unique_vas :=
    fold_left (fun acc sig =>
      if existsb (rfp_eqb_sig sig) acc then acc else List.app acc [sig])
    all_vas [] in
  let unique_lams :=
    fold_left (fun acc lam =>
      if existsb (rfp_eqb_term lam) acc then acc else List.app acc [lam])
    all_lams [] in
  let n_apps := List.length unique_vas in
  (* Declare fnApp_N wrappers for each unique var-app signature. *)
  _ <- monad_fold_left (fun idx sig =>
    let '(fn_type, arg_types, _) := sig in
    let nm   := "fnApp" ++ string_of_nat idx in
    let body := rfp_build_fnapp_body fn_type arg_types in
    _ <- tmMkDefinition nm body ;;
    tmReturn (S idx)) unique_vas 0 ;;
  (* Declare fnLam_N wrappers for each unique closed lambda. *)
  _ <- monad_fold_left (fun idx lam =>
    let nm := "fnLam" ++ string_of_nat idx in
    _ <- tmMkDefinition nm lam ;;
    tmReturn (S idx)) unique_lams n_apps ;;
  (* Build substitution maps. *)
  let sig_to_kn :=
    mapi (fun i sig =>
      let '(fn_type, arg_types, _) := sig in
      (fn_type, arg_types, (cur_mp, "fnApp" ++ string_of_nat i)))
    unique_vas in
  let lam_to_kn :=
    mapi (fun i lam =>
      (lam, (cur_mp, "fnLam" ++ string_of_nat (n_apps + i))))
    unique_lams in
  let kn_rename :=
    List.map (fun kn => (kn, (fst kn, snd kn ++ "removeFnPos"))) unique_kns in
  (* Topo-sort unique_kns so that blocks referenced by others are declared first.
     Without this, a block like bigStepTrremoveFnPos (which references stepremoveFnPos
     in its premises) would be declared before stepremoveFnPos exists. *)
  let minds_assoc := combine unique_kns minds in
  let block_id_map := List.map (fun kn => (kn, kn)) unique_kns in
  let sorted_kns :=
    topo_sort_kns unique_kns minds_assoc block_id_map [] [] (S #|unique_kns|) in
  let sorted_pairs :=
    flat_map (fun kn =>
      match find (fun p => eq_kername (fst p) kn) minds_assoc with
      | Some p => [p]
      | None   => []
      end)
    sorted_kns in
  (* Transform and re-declare each mutual block in dependency order. *)
  monad_fold_left (fun _ p =>
    let kn   := fst p in
    let mind := snd p in
    let new_mind :=
      rfp_transform_mind kn cur_mp kn_rename sig_to_kn lam_to_kn mind in
    new_mind' <- tmEval all new_mind ;;
    tmMkInductivePreserveFinite new_mind')
  sorted_pairs tt.
Set Universe Checking.

(* ===================================================================== *)
(*  Arrow-type lifting set computation                                    *)
(* ===================================================================== *)

(** Is [t] a function (arrow) type? *)
Definition lat_is_arrow (t : term) : bool :=
  match t with tProd _ _ _ => true | _ => false end.

(** Is [t] a sigma2 (inductive) type — either plain or parametric application? *)
Definition lat_is_sigma2_term (t : term) : bool :=
  match t with
  | tInd _ _          => true
  | tApp (tInd _ _) _ => true
  | _                 => false
  end.

(** Deduplicate a list of terms using structural equality. *)
Definition lat_dedup_terms (ts : list term) : list term :=
  fold_left (fun acc t =>
    if existsb (rfp_eqb_term t) acc then acc else List.app acc [t])
  ts [].


(** Like [lat_compute_dep_edges] but uses full terms on both sides and handles
    parametric sigma2 types ([tApp (tInd _ _) _]).  All four edge categories
    are returned as [term * term] pairs; direction is input left, output right.
    - [i2i_edges] : (sigma2_in, sigma2_out)
    - [a2i_edges] : (arrow_in,  sigma2_out)
    - [i2a_edges] : (sigma2_in, arrow_out)
    - [a2a_edges] : (arrow_in,  arrow_out) *)
Definition lat_compute_dep_edges2
    (fn_app_infos : list (kername * list term * term))
    : list (term * term) * list (term * term) *
      list (term * term) * list (term * term) :=
  fold_left
    (fun '(i2i, a2i, i2a, a2a) fi =>
      let arg_types := snd (fst fi) in
      let ret_type  := snd fi in
      fold_left (fun '(i2i_, a2i_, i2a_, a2a_) at_ =>
        if rfp_eqb_term at_ ret_type then (i2i_, a2i_, i2a_, a2a_)
        else
          let at_is_s2  := lat_is_sigma2_term at_ in
          let ret_is_s2 := lat_is_sigma2_term ret_type in
          let e_new     := (at_, ret_type) in
          let dup lst   :=
            existsb (fun e2 =>
              andb (rfp_eqb_term (fst e2) (fst e_new))
                   (rfp_eqb_term (snd e2) (snd e_new))) lst in
          if andb at_is_s2 ret_is_s2 then
            if dup i2i_ then (i2i_, a2i_, i2a_, a2a_)
            else (List.app i2i_ [e_new], a2i_, i2a_, a2a_)
          else if andb (lat_is_arrow at_) ret_is_s2 then
            if dup a2i_ then (i2i_, a2i_, i2a_, a2a_)
            else (i2i_, List.app a2i_ [e_new], i2a_, a2a_)
          else if andb at_is_s2 (lat_is_arrow ret_type) then
            if dup i2a_ then (i2i_, a2i_, i2a_, a2a_)
            else (i2i_, a2i_, List.app i2a_ [e_new], a2a_)
          else if andb (lat_is_arrow at_) (lat_is_arrow ret_type) then
            if dup a2a_ then (i2i_, a2i_, i2a_, a2a_)
            else (i2i_, a2i_, i2a_, List.app a2a_ [e_new])
          else (i2i_, a2i_, i2a_, a2a_)) arg_types (i2i, a2i, i2a, a2a))
    fn_app_infos ([], [], [], []).

(** One step of the combined arrow-inductive closure:
    - Arrows pull in inductive deps (via a2i_edges).
    - Inductives pull in arrow deps (via i2a_edges). *)
Definition lat_closure_step
    (arrow_types : list term)
    (type_kns    : list kername)
    (a2i_edges   : list (term * kername))
    (i2a_edges   : list (kername * term))
    : list term * list kername :=
  let new_ind_from_arrows :=
    dedup_kns (flat_map (fun ar =>
      flat_map (fun e =>
        if rfp_eqb_term (fst e) ar then [snd e] else [])
      a2i_edges) arrow_types) in
  let new_type_kns :=
    fold_left (fun acc kn =>
      if existsb (eq_kername kn) acc then acc else List.app acc [kn])
    new_ind_from_arrows type_kns in
  let new_arrows_from_inds :=
    lat_dedup_terms (flat_map (fun kn =>
      flat_map (fun e =>
        if eq_kername (fst e) kn then [snd e] else [])
      i2a_edges) new_type_kns) in
  let new_arrow_types :=
    fold_left (fun acc ar =>
      if existsb (rfp_eqb_term ar) acc then acc else List.app acc [ar])
    new_arrows_from_inds arrow_types in
  (new_arrow_types, new_type_kns).

(** Iterate [lat_closure_step] until both sets stop growing. *)
Fixpoint lat_closure_fix
    (arrow_types : list term)
    (type_kns    : list kername)
    (a2i_edges   : list (term * kername))
    (i2a_edges   : list (kername * term))
    (fuel        : nat)
    : list term * list kername :=
  match fuel with
  | 0 => (arrow_types, type_kns)
  | S f =>
    let '(arrow', type_kns') :=
      lat_closure_step arrow_types type_kns a2i_edges i2a_edges in
    if andb (Nat.eqb #|arrow'| #|arrow_types|)
            (Nat.eqb #|type_kns'| #|type_kns|)
    then (arrow', type_kns')
    else lat_closure_fix arrow' type_kns' a2i_edges i2a_edges f
  end.

(** One step of the fully unified closure.  All four edge kinds are treated
    symmetrically: a new node in either set triggers expansion in all
    directions.
    - [i2i_edges] sigma2 → sigma2  (structural / mode-derived deps)
    - [a2i_edges] arrow  → sigma2
    - [i2a_edges] sigma2 → arrow
    - [a2a_edges] arrow  → arrow *)
Definition lat_unified_closure_step
    (arrow_types : list term)
    (type_kns    : list kername)
    (i2i_edges   : list (kername * kername))
    (a2i_edges   : list (term * kername))
    (i2a_edges   : list (kername * term))
    (a2a_edges   : list (term * term))
    : list term * list kername :=
  let new_kns_i2i :=
    flat_map (fun e =>
      if andb (existsb (eq_kername (fst e)) type_kns)
              (negb (existsb (eq_kername (snd e)) type_kns))
      then [snd e] else []) i2i_edges in
  let new_kns_a2i :=
    flat_map (fun e =>
      if andb (existsb (rfp_eqb_term (fst e)) arrow_types)
              (negb (existsb (eq_kername (snd e)) type_kns))
      then [snd e] else []) a2i_edges in
  let new_kns := dedup_kns (List.app new_kns_i2i new_kns_a2i) in
  let new_arrows_i2a :=
    flat_map (fun e =>
      if andb (existsb (eq_kername (fst e)) type_kns)
              (negb (existsb (rfp_eqb_term (snd e)) arrow_types))
      then [snd e] else []) i2a_edges in
  let new_arrows_a2a :=
    flat_map (fun e =>
      if andb (existsb (rfp_eqb_term (fst e)) arrow_types)
              (negb (existsb (rfp_eqb_term (snd e)) arrow_types))
      then [snd e] else []) a2a_edges in
  let new_arrows := lat_dedup_terms (List.app new_arrows_i2a new_arrows_a2a) in
  (lat_dedup_terms (List.app arrow_types new_arrows),
   dedup_kns (List.app type_kns new_kns)).

Fixpoint lat_unified_closure_fix
    (arrow_types : list term)
    (type_kns    : list kername)
    (i2i_edges   : list (kername * kername))
    (a2i_edges   : list (term * kername))
    (i2a_edges   : list (kername * term))
    (a2a_edges   : list (term * term))
    (fuel        : nat)
    : list term * list kername :=
  match fuel with
  | 0 => (arrow_types, type_kns)
  | S f =>
    let '(arrow', kns') :=
      lat_unified_closure_step arrow_types type_kns i2i_edges a2i_edges i2a_edges a2a_edges in
    if andb (Nat.eqb #|arrow'| #|arrow_types|)
            (Nat.eqb #|kns'| #|type_kns|)
    then (arrow', kns')
    else lat_unified_closure_fix arrow' kns' i2i_edges a2i_edges i2a_edges a2a_edges f
  end.

(** Like [lat_unified_closure_step] but all four edge lists use [(term * term)]
    and the sigma2 set is [list term] (not [list kername]), so parametric types
    like [tApp (tInd list_kn) [sinstr]] are tracked as full terms.
    [rfp_eqb_term] is used for every membership test. *)
Definition lat_unified_closure_step2
    (arrow_types  : list term)
    (sigma2_types : list term)
    (i2i_edges    : list (term * term))
    (a2i_edges    : list (term * term))
    (i2a_edges    : list (term * term))
    (a2a_edges    : list (term * term))
    : list term * list term :=
  let new_s2_i2i :=
    flat_map (fun e =>
      if andb (existsb (rfp_eqb_term (fst e)) sigma2_types)
              (negb (existsb (rfp_eqb_term (snd e)) sigma2_types))
      then [snd e] else []) i2i_edges in
  let new_s2_a2i :=
    flat_map (fun e =>
      if andb (existsb (rfp_eqb_term (fst e)) arrow_types)
              (negb (existsb (rfp_eqb_term (snd e)) sigma2_types))
      then [snd e] else []) a2i_edges in
  let new_sigma2 :=
    lat_dedup_terms (List.app new_s2_i2i new_s2_a2i) in
  let new_arr_i2a :=
    flat_map (fun e =>
      if andb (existsb (rfp_eqb_term (fst e)) sigma2_types)
              (negb (existsb (rfp_eqb_term (snd e)) arrow_types))
      then [snd e] else []) i2a_edges in
  let new_arr_a2a :=
    flat_map (fun e =>
      if andb (existsb (rfp_eqb_term (fst e)) arrow_types)
              (negb (existsb (rfp_eqb_term (snd e)) arrow_types))
      then [snd e] else []) a2a_edges in
  let new_arrows :=
    lat_dedup_terms (List.app new_arr_i2a new_arr_a2a) in
  (lat_dedup_terms (List.app arrow_types new_arrows),
   lat_dedup_terms (List.app sigma2_types new_sigma2)).

Fixpoint lat_unified_closure_fix2
    (arrow_types  : list term)
    (sigma2_types : list term)
    (i2i_edges    : list (term * term))
    (a2i_edges    : list (term * term))
    (i2a_edges    : list (term * term))
    (a2a_edges    : list (term * term))
    (fuel         : nat)
    : list term * list term :=
  match fuel with
  | 0 => (arrow_types, sigma2_types)
  | S f =>
    let '(arrow', sigma2') :=
      lat_unified_closure_step2
        arrow_types sigma2_types i2i_edges a2i_edges i2a_edges a2a_edges in
    if andb (Nat.eqb #|arrow'|  #|arrow_types|)
            (Nat.eqb #|sigma2'| #|sigma2_types|)
    then (arrow', sigma2')
    else lat_unified_closure_fix2 arrow' sigma2' i2i_edges a2i_edges i2a_edges a2a_edges f
  end.

(** Collect all arrow types that appear as the [decl_type] of any constructor
    argument in [mind].  These create a structural dependency: [mind] depends
    on every arrow type that appears in its constructors' signatures. *)
Definition lat_collect_arrow_types_from_mind
    (mind : mutual_inductive_body) : list term :=
  lat_dedup_terms (flat_map (fun oib =>
    flat_map (fun c =>
      flat_map (fun d =>
        if lat_is_arrow d.(decl_type) then [d.(decl_type)] else [])
      c.(cstr_args))
    oib.(ind_ctors))
  mind.(ind_bodies)).

(** Monadic BFS over inductive types.  For each [kn] in the worklist:
    - quote [kn] and collect arrow types from constructor argument types
      (structural dependency rule);
    - collect arrow types from [i2a_edges] (function-application rule);
    - for each newly-added arrow type, look up [a2i_edges] and add any
      previously-unseen inductive types to the worklist.
    Visited inductives are tracked in [explored] to avoid re-processing. *)
Unset Universe Checking.
Polymorphic Fixpoint lat_monadic_closure
    (worklist    : list kername)
    (explored    : list kername)
    (arrow_types : list term)
    (type_kns    : list kername)
    (a2i_edges   : list (term * kername))
    (i2a_edges   : list (kername * term))
    (fuel        : nat)
    : TemplateMonad (list term * list kername) :=
  match fuel with
  | 0 => tmReturn (arrow_types, type_kns)
  | S f =>
    match worklist with
    | [] => tmReturn (arrow_types, type_kns)
    | kn :: rest =>
      if existsb (eq_kername kn) explored
      then lat_monadic_closure rest explored arrow_types type_kns
             a2i_edges i2a_edges f
      else
        mind <- tmQuoteInductive kn ;;
        (* Structural rule: arrow types in constructor argument types *)
        let ctor_arrows := lat_collect_arrow_types_from_mind mind in
        (* Function-application rule: i2a_edges for this inductive *)
        let fn_arrows :=
          flat_map (fun e =>
            if eq_kername (fst e) kn then [snd e] else []) i2a_edges in
        let all_new_arrows :=
          filter (fun ar => negb (existsb (rfp_eqb_term ar) arrow_types))
            (lat_dedup_terms (List.app ctor_arrows fn_arrows)) in
        let new_arrow_types :=
          fold_left (fun acc ar =>
            if existsb (rfp_eqb_term ar) acc then acc else List.app acc [ar])
          all_new_arrows arrow_types in
        (* a2i_edges: newly-added arrow types may pull in more inductives *)
        let new_ind_from_arrows :=
          filter (fun kn' =>
            andb (negb (existsb (eq_kername kn') type_kns))
                 (negb (existsb (eq_kername kn') rest)))
            (dedup_kns (flat_map (fun ar =>
              flat_map (fun e =>
                if rfp_eqb_term (fst e) ar then [snd e] else []) a2i_edges)
              all_new_arrows)) in
        let new_type_kns :=
          fold_left (fun acc kn' =>
            if existsb (eq_kername kn') acc then acc else List.app acc [kn'])
          new_ind_from_arrows type_kns in
        lat_monadic_closure
          (List.app rest new_ind_from_arrows)
          (kn :: explored)
          new_arrow_types
          new_type_kns
          a2i_edges i2a_edges f
    end
  end.
Set Universe Checking.

(** Collect the arrow types at the mode positions of a relation, using the
    snoc-list index convention of [ind_indices] (position 0 from the user maps
    to index [n_idx - 1] in the snoc-list). *)
Definition lat_arrow_types_from_mwi
    (mwi : (string * (list nat * list nat)) * list context_decl)
    : list term :=
  let in_pos  := fst (snd (fst mwi)) in
  let out_pos := snd (snd (fst mwi)) in
  let idx_ctx := snd mwi in
  let n_idx   := #|idx_ctx| in
  flat_map (fun i =>
    let snoc_p := n_idx - 1 - i in
    match nth_error idx_ctx snoc_p with
    | Some d => if lat_is_arrow d.(decl_type) then [d.(decl_type)] else []
    | None   => []
    end)
  (List.app in_pos out_pos).

(** Compute the arrow-type lifting set given a [mode_map] and the inductive
    lifting set [type_kns] already computed by [preprocess_coind_types].
    Returns [(arrow_types, extended_type_kns)] where:
    - [arrow_types] is the set of closed arrow-type terms to lift;
    - [extended_type_kns] is [type_kns] possibly grown by arrow-to-inductive
      dependency edges. *)
Unset Universe Checking.
Polymorphic Definition compute_lifted_arrow_types
    (modes    : mode_map)
    (type_kns : list kername)
    (fuel     : nat)
    : TemplateMonad (list term * list kername) :=
  (* Step 1: resolve each mode entry to an inductive reference. *)
  rel_inds <- monad_map (fun p =>
    let nm := fst p in
    refs <- tmLocate nm ;;
    match find (fun g =>
      match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("compute_lifted_arrow_types: cannot locate '" ++ nm ++ "'")
    end) modes ;;
  (* Step 2: quote each distinct mutual block once. *)
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;;
    tmReturn (kn, mind)) rel_block_kns ;;
  (* Step 3: build modes_with_idx. *)
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => [] | Some oib => oib.(ind_indices)
          end
        end in
      ((fst mode_e, snd mode_e), idx_ctx))
    (combine modes rel_inds) in
  (* Step 4: collect fn_app_infos from all relation constructors. *)
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
    rel_block_minds) [] in
  let extra_fn_pairs :=
    fold_left (fun acc p =>
      let fn_kn := fst p in
      if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) fn_app_infos_base)
             (existsb (fun q => eq_kername (fst q) fn_kn) acc)
      then acc else List.app acc [p])
    (flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds) [] in
  extra_fn_infos <- monad_map (fun p =>
    let fn_kn := fst p in
    let n     := List.length (snd p) in
    cb <- tmQuoteConstant fn_kn false ;;
    let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
    tmReturn (fn_kn, decl_arg_types, ret_tp)) extra_fn_pairs ;;
  let fn_app_infos := List.app fn_app_infos_base extra_fn_infos in
  fn_app_infos <- tmEval all fn_app_infos ;;
  (* Step 5: initial arrow types = arrow-typed mode positions across all relations. *)
  let initial_arrow_types :=
    lat_dedup_terms (flat_map lat_arrow_types_from_mwi modes_with_idx) in
  (* Step 6: dependency edges from named function applications. *)
  let '(_, a2i_raw, i2a_raw, _) := lat_compute_dep_edges2 fn_app_infos in
  (* lat_monadic_closure expects kername-based edges; project the head kn
     from each sigma2 term (tInd or tApp (tInd) _). *)
  let a2i_edges : list (term * kername) :=
    flat_map (fun e =>
      match snd e with
      | tInd ind _          => [(fst e, inductive_mind ind)]
      | tApp (tInd ind _) _ => [(fst e, inductive_mind ind)]
      | _                   => []
      end) a2i_raw in
  let i2a_edges : list (kername * term) :=
    flat_map (fun e =>
      match fst e with
      | tInd ind _          => [(inductive_mind ind, snd e)]
      | tApp (tInd ind _) _ => [(inductive_mind ind, snd e)]
      | _                   => []
      end) i2a_raw in
  (* Step 7: seed the inductive worklist.
     Start with all type_kns already computed by preprocess_coind_types, so
     the monadic closure can scan their constructors for arrow types.
     Also immediately apply a2i_edges to initial_arrow_types to pull in any
     extra inductives that the initial arrow seeds depend on. *)
  let initial_ind_from_arrows :=
    filter (fun kn => negb (existsb (eq_kername kn) type_kns))
      (dedup_kns (flat_map (fun ar =>
        flat_map (fun e =>
          if rfp_eqb_term (fst e) ar then [snd e] else []) a2i_edges)
        initial_arrow_types)) in
  let combined_type_kns :=
    fold_left (fun acc kn =>
      if existsb (eq_kername kn) acc then acc else List.app acc [kn])
    initial_ind_from_arrows type_kns in
  (* Step 8: monadic BFS — visits every inductive in combined_type_kns,
     applies both the structural constructor rule and i2a_edges for arrows,
     then follows a2i_edges from any newly-added arrow types. *)
  r <- lat_monadic_closure
         combined_type_kns [] initial_arrow_types combined_type_kns
         a2i_edges i2a_edges (fuel * (S #|combined_type_kns|)) ;;
  let final_arrow_types := fst r in
  let final_type_kns    := snd r in
  tmReturn (final_arrow_types, final_type_kns).
Set Universe Checking.

(** Replace [t] with its lifted counterpart if one exists:
    - arrow types in [arr_name_pairs] → the corresponding lifted [fnTypeN] inductive
    - bare [tInd] knames in [ind_mapping]  → the corresponding lifted kname
    Only the top-level type is checked; compound types are not recursed into. *)
Definition lat_lift_type
    (arr_name_pairs : list (term * string))
    (ind_mapping    : list (kername * inductive))
    (cur_mp         : modpath)
    (t              : term)
    : term :=
  match find (fun p => rfp_eqb_term (fst p) t) arr_name_pairs with
  | Some (_, nm) =>
    tInd {| inductive_mind := (cur_mp, nm); inductive_ind := 0 |} []
  | None =>
    match t with
    | tInd ind us =>
      match find (fun p => eq_kername (fst p) (inductive_mind ind)) ind_mapping with
      | Some (_, new_ind) =>
        tInd new_ind us
      | None => t
      end
    | _ => t
    end
  end.

(** Inverse of [lat_lift_type]: map a lifted arrow-type inductive or lifted
    inductive back to the original type term. *)
Definition lat_unlift_type
    (arr_name_pairs : list (term * string))
    (ind_mapping    : list (kername * kername))
    (cur_mp         : modpath)
    (t              : term)
    : term :=
  match t with
  | tInd ind _ =>
    let kn := inductive_mind ind in
    match find (fun '(_, nm) => eq_kername (cur_mp, nm) kn) arr_name_pairs with
    | Some (orig_arr_t, _) => orig_arr_t
    | None =>
      match find (fun '(_, new_kn) => eq_kername new_kn kn) ind_mapping with
      | Some (old_kn, _) =>
        tInd {| inductive_mind := old_kn; inductive_ind := inductive_ind ind |} []
      | None => t
      end
    end
  | _ => t
  end.

(** Build the [mutual_inductive_body] for one lifted arrow type.
    [arr_t]  : the original (closed) arrow-type term.
    [name]   : sequential name, e.g. ["fnType0"].
    Constructors (in order):
      [relNmAnOP]      — one per (relation, output-position) whose output type
                         equals [arr_t]; input-position types are lifted.
      [nameLiftCstr]   — embeds the original arrow type: [arr_t -> liftedType].
      [fnNmLiftedCstr] — one per entry in [fn_app_infos] whose return type equals
                         [arr_t]; each arg type is lifted via [lat_lift_type]. *)
Definition lat_build_arrow_ind
    (arr_t          : term)
    (name           : string)
    (arr_name_pairs : list (term * string))
    (ind_mapping    : list (kername * inductive))
    (fn_app_infos   : list (kername * list term * term))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    (cur_mp         : modpath)
    : mutual_inductive_body :=
  let anon_b := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let lift_t  := lat_lift_type arr_name_pairs ind_mapping cur_mp in
  (* Helpers to replace tInd {(cur_mp, name), 0} with the correct tRel in
     cstr_args (depth-sensitive) and cstr_type (depth 0, recursive).
     This mirrors the s3args/s3t mechanism in make_lifted_mind: fnType0 is not
     yet in the environment when tmMkInductivePreserveFinite is called, so
     self-references must be expressed as De Bruijn variables. *)
  let s3t t :=
    subst_block_inds_to_rels (cur_mp, name) 1 0 t in
  let s3args args :=
    let n_a := #|args| in
    mapi (fun snoc_i d =>
      {| decl_name := d.(decl_name);
         decl_body := d.(decl_body);
         decl_type := subst_block_inds_to_rels (cur_mp, name) 1 (n_a - 1 - snoc_i) d.(decl_type) |})
    args in
  (* Animation constructors: relNmAnOP for each out-position whose type = arr_t. *)
  let anim_ctors :=
    flat_map (fun mwi =>
      let nm      := fst (fst mwi) in
      let in_pos  := fst (snd (fst mwi)) in
      let out_pos := snd (snd (fst mwi)) in
      let idx_ctx := snd mwi in
      let n_idx   := #|idx_ctx| in
      flat_map (fun op =>
        let snoc_op := n_idx - 1 - op in
        match nth_error idx_ctx snoc_op with
        | None => []
        | Some od =>
          if rfp_eqb_term arr_t od.(decl_type) then
            (* Build input decls in user (left-to-right) order, then reverse
               to snoc order for cstr_args / it_mkProd_or_LetIn. *)
            let input_decls :=
              List.rev (snd (fold_left (fun '(depth, acc) ip =>
                let snoc_ip := n_idx - 1 - ip in
                match nth_error idx_ctx snoc_ip with
                | None => (S depth, acc)
                | Some d =>
                  (S depth,
                   List.app acc [{| decl_name :=
                                      {| binder_name     := nNamed ("v" ++ string_of_nat depth);
                                         binder_relevance := Relevant |};
                                    decl_body := None;
                                    decl_type := lift_t d.(decl_type) |}])
                end)
              in_pos (0, []))) in
            let n_args := #|input_decls| in
            [{| cstr_name    := nm ++ "An" ++ string_of_nat op;
                cstr_args    := s3args input_decls;
                cstr_indices := [];
                cstr_type    := s3t (it_mkProd_or_LetIn input_decls (tRel n_args));
                cstr_arity   := n_args |}]
          else []
        end) out_pos)
    modes_with_idx in
  (* LiftCstr: embed the original arrow type. *)
  let lift_arg :=
    {| decl_name := anon_b; decl_body := None; decl_type := arr_t |} in
  let lift_cstr :=
    {| cstr_name    := name ++ "LiftCstr";
       cstr_args    := [lift_arg];
       cstr_indices := [];
       cstr_type    := it_mkProd_or_LetIn [lift_arg] (tRel 1);
       cstr_arity   := 1 |} in
  (* LiftedCstr: one per named function whose return type equals arr_t. *)
  let lifted_fn_ctors :=
    flat_map (fun '((fn_kn, arg_types), ret_type) =>
      if rfp_eqb_term ret_type arr_t then
        (* arg_types from fn_app_infos is in natural (left-to-right) order;
           reverse to snoc order for cstr_args. *)
        let lifted_args :=
          List.rev (List.map (fun t =>
            {| decl_name := anon_b; decl_body := None; decl_type := lift_t t |})
          arg_types) in
        let n_args := #|lifted_args| in
        [{| cstr_name    := snd fn_kn ++ "LiftedCstr";
            cstr_args    := s3args lifted_args;
            cstr_indices := [];
            cstr_type    := s3t (it_mkProd_or_LetIn lifted_args (tRel n_args));
            cstr_arity   := n_args |}]
      else [])
    fn_app_infos in
  let oib :=
    {| ind_name      := name;
       ind_indices   := [];
       ind_sort      := Sort.type0;
       ind_type      := tSort Sort.type0;
       ind_kelim     := IntoAny;
       ind_ctors     := List.app anim_ctors (List.app [lift_cstr] lifted_fn_ctors);
       ind_projs     := [];
       ind_relevance := Relevant |} in
  {| ind_finite    := Finite;
     ind_npars     := 0;
     ind_universes := Monomorphic_ctx;
     ind_variance  := None;
     ind_params    := [];
     ind_bodies    := [oib] |}.

(* ================================================================== *)
(** ** Type aliases for preprocess_all_lifting_types sub-functions   *)
(* ================================================================== *)

(** A quoted mutual inductive block: its kn paired with its body. *)
Definition quoted_mind     := (kername * mutual_inductive_body)%type.

(** A parametric application: head inductive kn + concrete type args.
    E.g. [(list_kn, [sinstr_term])] for [list sinstr]. *)
Definition ind_app         := (kername * list term)%type.

(** Specialization witness: an [ind_app] and the kn of the specialised
    inductive declared for it. E.g. [(list,[sinstr]) ↦ listsinstr_kn]. *)
Definition spec_pair       := (ind_app * kername)%type.

(** Named-function dependency record: [(kn, arg_types, ret_type)].
    Represents a named constant that appears in relation constructor bodies;
    its lifting determines which types enter σ2 / arrow sets.
    E.g. [(evalExp_kn, [nat→nat; exp], nat)]. *)
Definition fn_app_info     := (kername * list term * term)%type.

(** Arrow type term paired with the [fnTypeN] name assigned to it.
    E.g. [(string→nat term, "fnType0")]. *)
Definition arr_name_pair   := (term * string)%type.

(** Topo-sort edge: [(dependent_kn, dependency_kn)].
    [dependent_kn] must be declared AFTER [dependency_kn]. *)
Definition topo_edge       := (kername * kername)%type.

(** Lifting-set a2i edge (lifting_rules.md §a2i): function with arrow INPUT
    Ar and inductive OUTPUT B → edge [(Ar, B_kn)].
    Semantics: when Ar ∈ arrow lifting set, add B to sigma2. *)
Definition a2i_edge        := (term * kername)%type.

(** Lifting-set i2a edge (lifting_rules.md §i2a): function with inductive
    INPUT B and arrow OUTPUT Ar → edge [(B_kn, Ar)].
    Semantics: when B ∈ sigma2, add Ar to the arrow lifting set. *)
Definition i2a_edge        := (kername * term)%type.

(** Lifting-set a2a edge (lifting_rules.md §a2a): function with arrow INPUT
    Ar1 and arrow OUTPUT Ar2 (Ar1 ≠ Ar2) → edge [(Ar2, Ar1)].
    Semantics: when Ar2 ∈ arrow lifting set, add Ar1 to the arrow lifting set. *)
Definition a2a_edge        := (term * term)%type.

(** Sigma2 type kn paired with its declared lifted inductive.
    This is the type of [actual_mapping] returned by the preprocessor. *)
Definition sigma2_ind_pair := (kername * inductive)%type.

(** Parametric application paired with its declared lifted inductive.
    This is the type of [app_kn_mapping] returned by the preprocessor.
    E.g. [(list_kn, [sinstr_term]) ↦ listsinstr'_inductive]. *)
Definition app_ind_pair    := (kername * list term * inductive)%type.

(** Arrow pseudo-kn paired with the kn of its declared [fnTypeK] inductive.
    This is the type of [lat_ind_mapping] returned by the preprocessor. *)
Definition lat_ind_pair    := (kername * kername)%type.

(** Mode map entry annotated with the relation's quantified-variable index
    context (one [context_decl] per ∀-bound index variable in the
    relation's type). *)
Definition mode_with_idx   :=
  ((string * (list nat * list nat)) * list context_decl)%type.

(** A strongly-connected component in the sigma2 dependency graph:
    a list of sigma2 kns that must be declared in one mutual block.
    E.g. [[listsinstr_kn; listnat_kn]] for stack_step. *)
Definition sigma2_scc      := list kername.

(* ================================================================== *)
(** ** Unified lifting preprocessor: individual sub-functions        *)
(* ================================================================== *)

(** [build_rel_context] — Phases A / A.2 / A.3.

    Quotes the relation bodies, builds [modes_with_idx], and collects
    the raw type seeds for the lifting set computation.

    Returns:
    - [rel_block_minds]      quoted mutual blocks for all referenced relations
    - [modes_with_idx]       each mode entry annotated with its index-variable ctx
    - [rel_kns]              kns of the relation blocks (excluded from σ2 set)
    - [ctor_eq_kns_raw]      head kns of types in equality premises
                             (e.g. [nat_kn] from [evalExp vs e = 0])
    - [arg_kns_raw]          head kns of types at mode-position indices
                             (e.g. [cmd_kn] from evalCmd input pos 1)
    - [ctor_eq_ind_apps_raw] parametric ind-apps in equality premises
                             (e.g. [(list_kn,[sinstr_t])] from list-equality premises) *)
Unset Universe Checking.
Polymorphic Definition build_rel_context
    (modes : mode_map)
    : TemplateMonad
        (list quoted_mind
         * list mode_with_idx
         * list kername
         * list kername
         * list kername
         * list ind_app) :=
  rel_inds <- monad_map (fun p =>
    let nm := fst p in
    refs <- tmLocate nm ;;
    match find (fun g =>
      match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("build_rel_context: cannot locate '" ++ nm ++ "'")
    end) modes ;;
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;; tmReturn (kn, mind)) rel_block_kns ;;
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => [] | Some oib => oib.(ind_indices)
          end
        end in
      ((fst mode_e, snd mode_e), idx_ctx))
    (combine modes rel_inds) in
  let rel_kns := dedup_kns (List.map inductive_mind rel_inds) in
  let ctor_eq_kns_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_kns c.(cstr_type)) oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  let ctor_eq_ind_apps_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_ind_apps c.(cstr_type)) oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  let arg_kns_raw :=
    flat_map (fun mwi =>
      let in_pos  := fst (snd (fst mwi)) in
      let out_pos := snd (snd (fst mwi)) in
      let idx_ctx := snd mwi in
      flat_map (fun i =>
        match nth_error idx_ctx i with
        | Some d =>
          match d.(decl_type) with
          | tInd ind _  => [inductive_mind ind]
          | tApp f' _   =>
            match f' with tInd ind _ => [inductive_mind ind] | _ => [] end
          | _ => []
          end
        | None => []
        end)
      (List.app in_pos out_pos))
    modes_with_idx in
  tmReturn (rel_block_minds, modes_with_idx, rel_kns,
            ctor_eq_kns_raw, arg_kns_raw, ctor_eq_ind_apps_raw).
Set Universe Checking.

(** [declare_spec_pairs] — Phase A.4.

    For every parametric inductive application (e.g. [list nat]) that appears
    in mode-position index types or equality-premise ind-apps, declare a
    monomorphic specialisation (e.g. [listnat]) and return the mapping
    [(ind_app ↦ specialised_kn)].

    An entry is skipped when the head inductive is non-parametric
    ([ind_npars = 0]).  Duplicates in the input are deduplicated before
    processing so each specialisation is declared at most once. *)
Unset Universe Checking.
Polymorphic Definition declare_spec_pairs
    (modes_with_idx       : list mode_with_idx)
    (ctor_eq_ind_apps_raw : list ind_app)
    : TemplateMonad (list spec_pair) :=
  cur_mp <- tmCurrentModPath tt ;;
  let raw_ind_apps :=
    dedup_ind_apps
      ((flat_map (fun mwi =>
          flat_map (fun d => collect_ind_apps_toplevel d.(decl_type)) (snd mwi))
        modes_with_idx)
       ++ ctor_eq_ind_apps_raw) in
  spec_kn_pairs <- monad_fold_left (fun acc entry =>
    let head_kn     := fst entry in
    let arg_terms_e := snd entry in
    head_mind <- tmQuoteInductive head_kn ;;
    if Nat.eqb head_mind.(ind_npars) 0 then tmReturn acc
    else
      let spec_name :=
        fold_left (fun s t => s ++ ind_type_name t) arg_terms_e (snd head_kn) in
      let concrete_args := List.rev arg_terms_e in
      spec_body <- tmEval all (specialize_mind head_mind head_kn concrete_args spec_name) ;;
      tmMkInductivePreserveFinite spec_body ;;
      refs <- tmLocate spec_name ;;
      let spec_kn :=
        match find (fun g => match g with IndRef _ => true | _ => false end) refs with
        | Some (IndRef ind) => inductive_mind ind
        | _                 => (cur_mp, spec_name)
        end in
      tmReturn (List.app acc [(entry, spec_kn)]))
    raw_ind_apps [] ;;
  spec_kn_pairs <- tmEval all spec_kn_pairs ;;
  tmReturn spec_kn_pairs.
Set Universe Checking.


(** [collect_struct_edges] — Phase A.6.

    Computes structural edges by a uniform right-to-left BFS over a single
    worklist of [term]s, treating every type (σ2 inductive or arrow) the same
    way.  All fn-rule edges are converted to [(term * term)] pairs upfront so
    the loop has one unified edge list.

    For each term T in the worklist:
    - if T = [tInd ind _]: scan the ind_body at [inductive_ind ind] for
      constructor field types F and emit structural edge (F, T):
        * F = tInd → struct σ2→σ2 edge
        * F = tProd/arrow → struct arr→σ2 edge
    - for ALL T (inductive or arrow): look up fn_edges (C, T) right-to-left
      and add every trigger C to the worklist.

    This is uniform: a2a edges (Ar1, Ar2) are handled identically to i2i
    edges (B, C) — when Ar2 is processed from the worklist we find Ar1 and
    add it; when Ar1 is processed we may find i2a (B, Ar1) and add B.

    Returns [(struct_i2i_edges, struct_a2i_edges)] split from the raw edges. *)
Unset Universe Checking.
Polymorphic Fixpoint collect_struct_edges_loop
    (worklist  : list term)
    (scanned   : list term)
    (edges_acc : list (term * term))
    (fn_edges  : list (term * term))
    (fuel      : nat)
    : TemplateMonad (list (term * term)) :=
  match fuel with
  | 0 => tmFail "collect_struct_edges_loop: fuel exhausted before worklist empty"
  | S f =>
    match worklist with
    | [] => tmReturn edges_acc
    | t :: rest =>
      if existsb (rfp_eqb_term t) scanned
      then collect_struct_edges_loop rest scanned edges_acc fn_edges f
      else
        (* Extract inductive info if t is a σ2 type; None for arrow types *)
        let maybe_ind := match t with tInd ind _ => Some ind | _ => None end in
        new_struct_edges <-
          match maybe_ind with
          | None => tmReturn []
          | Some ind =>
            mind <- tmQuoteInductive (inductive_mind ind) ;;
            let oibs :=
              match nth_error mind.(ind_bodies) (inductive_ind ind) with
              | Some b => [b]
              | None   => mind.(ind_bodies)
              end in
            tmReturn (flat_map (fun oib =>
              flat_map (fun c =>
                flat_map (fun d =>
                  let f_t := d.(decl_type) in
                  match f_t with
                  | tInd _ _ =>
                    if negb (rfp_eqb_term f_t t) then [(f_t, t)] else []
                  | tProd _ _ _ =>
                    if negb (rfp_eqb_term f_t t) then [(f_t, t)] else []
                  | _ => []
                  end) c.(cstr_args)) oib.(ind_ctors)) oibs)
          end ;;
        (* Right-to-left: for all fn edges (C, t), add C to worklist *)
        let fn_triggers :=
          flat_map (fun e =>
            if rfp_eqb_term (snd e) t then [fst e] else []) fn_edges in
        let already_seen := List.app scanned (t :: rest) in
        let fresh :=
          filter (fun x => negb (existsb (rfp_eqb_term x) already_seen))
                 (lat_dedup_terms
                   (List.app (List.map fst new_struct_edges)
                              fn_triggers)) in
        collect_struct_edges_loop
          (List.app rest fresh)
          (List.app scanned [t])
          (List.app edges_acc new_struct_edges)
          fn_edges f
    end
  end.

(** Like [collect_struct_edges_loop] but handles parametric sigma2 types
    ([tApp (tInd _ _) _]) by calling [specialize_mind] on-the-fly.
    Field types matching [lat_is_sigma2_term] or [lat_is_arrow] are included.
    Fails with [tmFail] (reporting worklist length) when fuel is exhausted. *)
Polymorphic Fixpoint collect_struct_edges_loop2
    (worklist  : list term)
    (scanned   : list term)
    (edges_acc : list (term * term))
    (fn_edges  : list (term * term))
    (fuel      : nat)
    : TemplateMonad (list (term * term)) :=
  match fuel with
  | 0 =>
    tmFail ("collect_struct_edges_loop2: fuel exhausted, " ++
            string_of_nat (List.length worklist) ++ " items remain in worklist")
  | S f =>
    match worklist with
    | [] => tmReturn edges_acc
    | t :: rest =>
      if existsb (rfp_eqb_term t) scanned
      then collect_struct_edges_loop2 rest scanned edges_acc fn_edges f
      else
        new_struct_edges <-
          match t with
          | tInd ind _ =>
            mind <- tmQuoteInductive (inductive_mind ind) ;;
            let oibs :=
              match nth_error mind.(ind_bodies) (inductive_ind ind) with
              | Some b => [b]
              | None   => mind.(ind_bodies)
              end in
            tmReturn (flat_map (fun oib =>
              flat_map (fun c =>
                flat_map (fun d =>
                  let f_t := d.(decl_type) in
                  if andb (orb (lat_is_sigma2_term f_t) (lat_is_arrow f_t))
                          (negb (rfp_eqb_term f_t t))
                  then [(f_t, t)] else []) c.(cstr_args)) oib.(ind_ctors)) oibs)
          | tApp (tInd head _) app_args =>
            mind <- tmQuoteInductive (inductive_mind head) ;;
            let spec_mind :=
              specialize_mind mind (inductive_mind head) app_args "_spec" in
            let oibs :=
              match nth_error spec_mind.(ind_bodies) (inductive_ind head) with
              | Some b => [b]
              | None   => spec_mind.(ind_bodies)
              end in
            tmReturn (flat_map (fun oib =>
              flat_map (fun c =>
                flat_map (fun d =>
                  let f_t := d.(decl_type) in
                  if andb (orb (lat_is_sigma2_term f_t) (lat_is_arrow f_t))
                          (negb (rfp_eqb_term f_t t))
                  then [(f_t, t)] else []) c.(cstr_args)) oib.(ind_ctors)) oibs)
          | _ => tmReturn []
          end ;;
        let fn_triggers :=
          flat_map (fun e =>
            if rfp_eqb_term (snd e) t then [fst e] else []) fn_edges in
        let already_seen := List.app scanned (t :: rest) in
        let fresh :=
          filter (fun x => negb (existsb (rfp_eqb_term x) already_seen))
                 (lat_dedup_terms
                   (List.app (List.map fst new_struct_edges)
                              fn_triggers)) in
        collect_struct_edges_loop2
          (List.app rest fresh)
          (List.app scanned [t])
          (List.app edges_acc new_struct_edges)
          fn_edges f
    end
  end.

(** [get_field_types t] quotes the inductive named by [t] (plain or parametric),
    calls [specialize_mind] when [t = tApp (tInd ...) args], and returns the
    raw [decl_type] of every constructor field — unfiltered, so callers can
    inspect exactly what [specialize_mind] produces. *)
Polymorphic Definition get_field_types (t : term)
    : TemplateMonad (list term) :=
  match t with
  | tInd ind _ =>
    mind <- tmQuoteInductive (inductive_mind ind) ;;
    let oibs :=
      match nth_error mind.(ind_bodies) (inductive_ind ind) with
      | Some b => [b] | None => mind.(ind_bodies) end in
    tmReturn (flat_map (fun oib =>
      flat_map (fun c =>
        List.map (fun d => d.(decl_type)) c.(cstr_args))
      oib.(ind_ctors)) oibs)
  | tApp (tInd head _) app_args =>
    mind <- tmQuoteInductive (inductive_mind head) ;;
    let spec_mind :=
      specialize_mind mind (inductive_mind head) app_args "_spec" in
    let oibs :=
      match nth_error spec_mind.(ind_bodies) (inductive_ind head) with
      | Some b => [b] | None => spec_mind.(ind_bodies) end in
    tmReturn (flat_map (fun oib =>
      flat_map (fun c =>
        List.map (fun d => d.(decl_type)) c.(cstr_args))
      oib.(ind_ctors)) oibs)
  | _ => tmReturn []
  end.


(** Like [collect_all_lifting_edges] but takes only a [mode_map] and [fuel];
    all seed types, arrow types, and fn_app_infos are computed internally.
    Handles parametric sigma2 types via [lat_is_sigma2_term] and
    [collect_struct_edges_loop2] (no eager specialisation).

    Returns four edge lists: i2i, a2i, i2a, a2a — all as [(term * term)].
    Fails with [tmFail] if fuel is 0 or BFS fuel is exhausted. *)
Polymorphic Definition collect_all_lifting_edges2
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad (list (term * term) * list (term * term) *
                     list (term * term) * list (term * term)) :=
  if Nat.eqb fuel 0 then
    tmFail "collect_all_lifting_edges2: fuel exhausted before BFS started"
  else
  (* ── A.1: quote relation bodies, build modes_with_idx ─────────────── *)
  rel_inds <- monad_map (fun p =>
    let nm := fst p in
    refs <- tmLocate nm ;;
    match find (fun g =>
      match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("collect_all_lifting_edges2: cannot locate '" ++ nm ++ "'")
    end) modes ;;
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;; tmReturn (kn, mind)) rel_block_kns ;;
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => [] | Some oib => oib.(ind_indices)
          end
        end in
      ((fst mode_e, snd mode_e), idx_ctx))
    (combine modes rel_inds) in
  (* ── A.2: equality-premise types as full terms ─────────────────────── *)
  let kn_to_term kn :=
    tInd {| inductive_mind := kn; inductive_ind := 0 |} [] in
  let ind_app_to_term (entry : kername * list term) :=
    match snd entry with
    | []   => kn_to_term (fst entry)
    | args => tApp (kn_to_term (fst entry)) args
    end in
  let ctor_eq_terms_raw :=
    lat_dedup_terms
      (flat_map (fun km =>
        flat_map (fun oib =>
          flat_map (fun c =>
            List.map ind_app_to_term (collect_eq_arg_ind_apps c.(cstr_type)))
          oib.(ind_ctors))
        (snd km).(ind_bodies)) rel_block_minds) in
  let ctor_eq_arrow_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_arrows c.(cstr_type)) oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  (* ── A.3: sigma2 mode-position types as full terms ─────────────────── *)
  let arg_terms_raw :=
    lat_dedup_terms
      (flat_map (fun mwi =>
        let in_pos  := fst (snd (fst mwi)) in
        let out_pos := snd (snd (fst mwi)) in
        let idx_ctx := snd mwi in
        flat_map (fun i =>
          match nth_error idx_ctx i with
          | Some d =>
            let t := d.(decl_type) in
            if lat_is_sigma2_term t then [t] else []
          | None => []
          end)
        (List.app in_pos out_pos))
      modes_with_idx) in
  (* ── A.5: fn_app_infos (no eager specialisation needed) ────────────── *)
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
      (snd km).(ind_bodies)) rel_block_minds) [] in
  let extra_fn_pairs :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  let new_fn_pairs :=
    fold_left (fun acc p =>
      let fn_kn := fst p in
      if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) fn_app_infos_base)
             (existsb (fun q => eq_kername (fst q) fn_kn) acc)
      then acc else List.app acc [p])
    extra_fn_pairs [] in
  extra_fn_infos <- monad_map (fun p =>
    let fn_kn := fst p in
    let n     := List.length (snd p) in
    cb <- tmQuoteConstant fn_kn false ;;
    let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
    tmReturn (fn_kn, decl_arg_types, ret_tp)) new_fn_pairs ;;
  let fn_app_infos := List.app fn_app_infos_base extra_fn_infos in
  fn_app_infos <- tmEval all fn_app_infos ;;
  (* ── A.6 + B: seed types, build fn edge graph, BFS ─────────────────── *)
  let seed_arrow_raw :=
    lat_dedup_terms (List.app
      (flat_map lat_arrow_types_from_mwi modes_with_idx)
      ctor_eq_arrow_raw) in
  let '(i2i_fn, a2i_fn, i2a_fn, a2a_fn) :=
    lat_compute_dep_edges2 fn_app_infos in
  let fn_edges_all : list (term * term) :=
    List.app i2i_fn (List.app a2i_fn (List.app i2a_fn a2a_fn)) in
  let init_sigma2_terms :=
    lat_dedup_terms
      (filter lat_is_sigma2_term
        (List.app arg_terms_raw
        (List.app ctor_eq_terms_raw
          (List.map snd fn_app_infos)))) in
  let init_worklist :=
    lat_dedup_terms (List.app init_sigma2_terms seed_arrow_raw) in
  init_struct_edges <- monad_fold_left (fun acc t =>
    match t with
    | tInd ind _ =>
      mind <- tmQuoteInductive (inductive_mind ind) ;;
      let oibs :=
        match nth_error mind.(ind_bodies) (inductive_ind ind) with
        | Some b => [b]
        | None   => mind.(ind_bodies)
        end in
      tmReturn (List.app acc
        (flat_map (fun oib =>
          flat_map (fun c =>
            flat_map (fun d =>
              let f_t := d.(decl_type) in
              if andb (orb (lat_is_sigma2_term f_t) (lat_is_arrow f_t))
                      (negb (rfp_eqb_term f_t t))
              then [(f_t, t)] else []) c.(cstr_args)) oib.(ind_ctors)) oibs))
    | tApp (tInd head _) app_args =>
      mind <- tmQuoteInductive (inductive_mind head) ;;
      let spec_mind :=
        specialize_mind mind (inductive_mind head) app_args "_spec" in
      let oibs :=
        match nth_error spec_mind.(ind_bodies) (inductive_ind head) with
        | Some b => [b]
        | None   => spec_mind.(ind_bodies)
        end in
      tmReturn (List.app acc
        (flat_map (fun oib =>
          flat_map (fun c =>
            flat_map (fun d =>
              let f_t := d.(decl_type) in
              if andb (orb (lat_is_sigma2_term f_t) (lat_is_arrow f_t))
                      (negb (rfp_eqb_term f_t t))
              then [(f_t, t)] else []) c.(cstr_args)) oib.(ind_ctors)) oibs))
    | _ => tmReturn acc
    end) init_sigma2_terms [] ;;
  let init_edges :=
    fold_left (fun acc e =>
      if existsb (fun e2 =>
           andb (rfp_eqb_term (fst e) (fst e2))
                (rfp_eqb_term (snd e) (snd e2))) acc
      then acc else List.app acc [e])
      init_struct_edges fn_edges_all in
  raw_edges <-
    collect_struct_edges_loop2 init_worklist [] init_edges fn_edges_all fuel ;;
  let dedup_raw :=
    fold_left (fun acc e =>
      if existsb (fun e2 =>
           andb (rfp_eqb_term (fst e) (fst e2))
                (rfp_eqb_term (snd e) (snd e2))) acc
      then acc else List.app acc [e]) raw_edges [] in
  let dedup_raw :=
    filter (fun e => negb (rfp_eqb_term (fst e) (snd e))) dedup_raw in
  let all_i2i :=
    filter (fun e => andb (lat_is_sigma2_term (fst e)) (lat_is_sigma2_term (snd e)))
           dedup_raw in
  let all_a2i :=
    filter (fun e => andb (lat_is_arrow (fst e)) (lat_is_sigma2_term (snd e)))
           dedup_raw in
  let all_i2a :=
    filter (fun e => andb (lat_is_sigma2_term (fst e)) (lat_is_arrow (snd e)))
           dedup_raw in
  let all_a2a :=
    filter (fun e => andb (lat_is_arrow (fst e)) (lat_is_arrow (snd e)))
           dedup_raw in
  tmReturn (all_i2i, all_a2i, all_i2a, all_a2a).
Set Universe Checking.

(* ================================================================== *)
(** ** Unified lifting preprocessor (sigma2 + arrow types)           *)
(* ================================================================== *)

(** Like [preprocess_coind_types] but also handles arrow-typed relation
    arguments.  Computes the combined dependency graph, topo-sorts all
    lifted types together, and declares them in the correct order.

    [modes] must use the [removeFnPos] relation names (e.g.
    ["evalCmdremoveFnPos"]) since [remove_from_fn_pos] must have already
    been called.

    Returns [(type_mapping, app_kn_mapping, arr_name_pairs, lat_ind_mapping)].
    - [type_mapping]    sigma2 kn → lifted [inductive]
    - [app_kn_mapping]  parametric app → lifted [inductive]
    - [arr_name_pairs]  arrow [term] → [fnTypeN] name string
    - [lat_ind_mapping] sigma2 kn → lifted kname (for [lat_lift_type]) *)

Unset Universe Checking.
(** [compute_lifting_set2 modes fuel] computes the sigma2 and arrow lifting
    sets using [collect_all_lifting_edges2] (no eager parametric
    specialisation) and [lat_unified_closure_fix2] (full-term sigma2 set).

    Unlike [compute_lifting_set], parametric types such as
    [tApp (tInd list_kn) [sinstr]] are tracked as full terms throughout —
    no [tmMkInductivePreserveFinite] calls are made.

    Returns [(sigma2_types, arrow_types)] as [list term * list term]. *)
Polymorphic Definition compute_lifting_set2
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad (list term * list term) :=
  (* ── A.1: quote relation bodies, build modes_with_idx ─────────────── *)
  rel_inds <- monad_map (fun p =>
    let nm := fst p in
    refs <- tmLocate nm ;;
    match find (fun g =>
      match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("compute_lifting_set2: cannot locate '" ++ nm ++ "'")
    end) modes ;;
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;; tmReturn (kn, mind)) rel_block_kns ;;
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => [] | Some oib => oib.(ind_indices)
          end
        end in
      ((fst mode_e, snd mode_e), idx_ctx))
    (combine modes rel_inds) in
  let rel_kns := dedup_kns (List.map inductive_mind rel_inds) in
  (* ── B: edges via collect_all_lifting_edges2 ──────────────────────── *)
  '(i2i, a2i, i2a, a2a) <- collect_all_lifting_edges2 modes fuel ;;
  (* ── C: sigma2 seed — full terms at sigma2 mode positions ─────────── *)
  let sigma2_seed_raw :=
    lat_dedup_terms (flat_map (fun mwi =>
      let in_pos  := fst (snd (fst mwi)) in
      let out_pos := snd (snd (fst mwi)) in
      let idx_ctx := snd mwi in
      flat_map (fun i =>
        match nth_error idx_ctx i with
        | Some d =>
          let t := d.(decl_type) in
          if lat_is_sigma2_term t then [t] else []
        | None => []
        end)
      (List.app in_pos out_pos))
    modes_with_idx) in
  (* Exclude terms whose head kn is one of the relation kns themselves. *)
  let sigma2_seed_no_rel :=
    filter (fun t =>
      match t with
      | tInd ind _          =>
        negb (existsb (eq_kername (inductive_mind ind)) rel_kns)
      | tApp (tInd ind _) _ =>
        negb (existsb (eq_kername (inductive_mind ind)) rel_kns)
      | _ => false
      end) sigma2_seed_raw in
  (* Exclude Prop inductives. *)
  seed_sigma2 <- monad_fold_left (fun acc t =>
    match t with
    | tInd ind _ | tApp (tInd ind _) _ =>
      mind <- tmQuoteInductive (inductive_mind ind) ;;
      if negb (is_prop_mind mind) then tmReturn (List.app acc [t])
      else tmReturn acc
    | _ => tmReturn acc
    end) sigma2_seed_no_rel [] ;;
  (* Arrow seed: arrow types at mode positions. *)
  let seed_arrow :=
    lat_dedup_terms (flat_map lat_arrow_types_from_mwi modes_with_idx) in
  (* ── D: unified fixpoint closure ────────────────────────────────────── *)
  let safe_fuel :=
    List.length i2i + List.length a2i +
    List.length i2a + List.length a2a + 5 in
  let '(arrow_types, sigma2_types) :=
    lat_unified_closure_fix2
      seed_arrow seed_sigma2 i2i a2i i2a a2a safe_fuel in
  sigma2_types <- tmEval all (lat_dedup_terms sigma2_types) ;;
  let arrow_types := lat_dedup_terms arrow_types in
  tmReturn (sigma2_types, arrow_types).

Polymorphic Definition preprocess_all_lifting_types
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad
        (list (kername * inductive) *
         list (kername * list term * inductive) *
         list (term * string) *
         list (kername * kername) *
         list ((string * (list nat * list nat)) * list context_decl) *
         list (kername * list term * term)) :=
  (* ── A: quote relation bodies, build modes_with_idx ──────────────── *)
  rel_inds <- monad_map (fun p =>
    let nm := fst p in
    refs <- tmLocate nm ;;
    match find (fun g =>
      match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("preprocess_all_lifting_types: cannot locate '" ++ nm ++ "'")
    end) modes ;;
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;; tmReturn (kn, mind)) rel_block_kns ;;
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => [] | Some oib => oib.(ind_indices)
          end
        end in
      ((fst mode_e, snd mode_e), idx_ctx))
    (combine modes rel_inds) in
  let rel_kns := dedup_kns (List.map inductive_mind rel_inds) in
  (* ── A.2: equality-premise types ───────────────────────────────────── *)
  let ctor_eq_kns_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_kns c.(cstr_type)) oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  let ctor_eq_ind_apps_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_ind_apps c.(cstr_type)) oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  let ctor_eq_arrow_raw :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map (fun c => collect_eq_arg_arrows c.(cstr_type)) oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  (* ── A.3: sigma2 mode-position types ───────────────────────────────── *)
  let arg_kns_raw :=
    flat_map (fun mwi =>
      let in_pos  := fst (snd (fst mwi)) in
      let out_pos := snd (snd (fst mwi)) in
      let idx_ctx := snd mwi in
      flat_map (fun i =>
        match nth_error idx_ctx i with
        | Some d =>
          match d.(decl_type) with
          | tInd ind _  => [inductive_mind ind]
          | tApp f' _   =>
            match f' with tInd ind _ => [inductive_mind ind] | _ => [] end
          | _ => []
          end
        | None => []
        end)
      (List.app in_pos out_pos))
    modes_with_idx in
  cur_mp <- tmCurrentModPath tt ;;
  (* ── A.5: fn_app_infos ─────────────────────────────────────────────── *)
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
      (snd km).(ind_bodies)) rel_block_minds) [] in
  let extra_fn_pairs :=
    flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies)) rel_block_minds in
  let new_fn_pairs :=
    fold_left (fun acc p =>
      let fn_kn := fst p in
      if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) fn_app_infos_base)
             (existsb (fun q => eq_kername (fst q) fn_kn) acc)
      then acc else List.app acc [p])
    extra_fn_pairs [] in
  extra_fn_infos <- monad_map (fun p =>
    let fn_kn := fst p in
    let n     := List.length (snd p) in
    cb <- tmQuoteConstant fn_kn false ;;
    let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
    tmReturn (fn_kn, decl_arg_types, ret_tp)) new_fn_pairs ;;
  let fn_app_infos := List.app fn_app_infos_base extra_fn_infos in
  fn_app_infos <- tmEval all fn_app_infos ;;
  (* ── A.6 + B: lifting edges via collect_all_lifting_edges2 ─────────── *)
  '(i2i_raw, a2i_raw, i2a_raw, a2a_raw) <- collect_all_lifting_edges2 modes fuel ;;
  (* ── C: sigma2 seed and unified BFS ────────────────────────────────── *)
  let sigma2_seed_raw :=
    lat_dedup_terms (flat_map (fun mwi =>
      let in_pos  := fst (snd (fst mwi)) in
      let out_pos := snd (snd (fst mwi)) in
      let idx_ctx := snd mwi in
      flat_map (fun i =>
        match nth_error idx_ctx i with
        | Some d =>
          let t := d.(decl_type) in
          if lat_is_sigma2_term t then [t] else []
        | None => []
        end)
      (List.app in_pos out_pos))
    modes_with_idx) in
  let sigma2_seed_no_rel :=
    filter (fun t =>
      match t with
      | tInd ind _          =>
        negb (existsb (eq_kername (inductive_mind ind)) rel_kns)
      | tApp (tInd ind _) _ =>
        negb (existsb (eq_kername (inductive_mind ind)) rel_kns)
      | _ => false
      end) sigma2_seed_raw in
  seed_sigma2 <- monad_fold_left (fun acc t =>
    match t with
    | tInd ind _ | tApp (tInd ind _) _ =>
      mind <- tmQuoteInductive (inductive_mind ind) ;;
      if negb (is_prop_mind mind) then tmReturn (List.app acc [t])
      else tmReturn acc
    | _ => tmReturn acc
    end) sigma2_seed_no_rel [] ;;
  let seed_arrow :=
    lat_dedup_terms (flat_map lat_arrow_types_from_mwi modes_with_idx) in
  let safe_fuel :=
    List.length i2i_raw + List.length a2i_raw +
    List.length i2a_raw + List.length a2a_raw + 5 in
  let '(arrow_types, sigma2_terms) :=
    lat_unified_closure_fix2
      seed_arrow seed_sigma2 i2i_raw a2i_raw i2a_raw a2a_raw safe_fuel in
  sigma2_terms <- tmEval all (lat_dedup_terms sigma2_terms) ;;
  let arrow_types := lat_dedup_terms arrow_types in
  (* ── A.4: parametric specialisations (only for types in sigma2_terms) ─ *)
  let raw_ind_apps :=
    dedup_ind_apps (flat_map (fun t =>
      match t with
      | tApp (tInd head_ind _) args => [(inductive_mind head_ind, args)]
      | _ => []
      end) sigma2_terms) in
  spec_kn_pairs <- monad_fold_left (fun acc entry =>
    let head_kn     := fst entry in
    let arg_terms_e := snd entry in
    head_mind <- tmQuoteInductive head_kn ;;
    if Nat.eqb head_mind.(ind_npars) 0 then tmReturn acc
    else
      let spec_name :=
        fold_left (fun s t => s ++ ind_type_name t) arg_terms_e (snd head_kn) in
      let concrete_args := List.rev arg_terms_e in
      spec_body <- tmEval all (specialize_mind head_mind head_kn concrete_args spec_name) ;;
      tmMkInductivePreserveFinite spec_body ;;
      refs <- tmLocate spec_name ;;
      let spec_kn :=
        match find (fun g => match g with IndRef _ => true | _ => false end) refs with
        | Some (IndRef ind) => inductive_mind ind
        | _                 => (cur_mp, spec_name)
        end in
      tmReturn (List.app acc [(entry, spec_kn)]))
    raw_ind_apps [] ;;
  spec_kn_pairs <- tmEval all spec_kn_pairs ;;
  let spec_kns := List.map snd spec_kn_pairs in
  (* Convert sigma2_terms → type_kns and raw term edges → kname-based edges. *)
  let term_to_sigma2_kn (t : term) : option kername :=
    match t with
    | tInd ind _ => Some (inductive_mind ind)
    | tApp (tInd head_ind _) args =>
      match find (fun e =>
        andb (eq_kername (fst (fst e)) (inductive_mind head_ind))
             (andb (Nat.eqb #|snd (fst e)| #|args|)
                   (forallb (fun ab => eqb_ind_type (fst ab) (snd ab))
                            (combine (snd (fst e)) args))))
        spec_kn_pairs with
      | Some e => Some (snd e)
      | None => None
      end
    | _ => None
    end in
  let type_kns := dedup_kns (flat_map (fun t =>
    match term_to_sigma2_kn t with
    | Some kn => [kn] | None => [] end) sigma2_terms) in
  let all_a2i_edges :=
    flat_map (fun e =>
      match term_to_sigma2_kn (snd e) with
      | Some kn => [(fst e, kn)] | None => [] end) a2i_raw in
  let i2a_edges :=
    flat_map (fun e =>
      match term_to_sigma2_kn (fst e) with
      | Some kn => [(kn, snd e)] | None => [] end) i2a_raw in
  (* ── D: arr_name_pairs, pseudo-knames, pre-mappings ──────────────────── *)
  let arr_name_pairs : list (term * string) :=
    snd (fold_left (fun '(i, acc) t =>
      (S i, List.app acc [(t, "fnType" ++ string_of_nat i)]))
    arrow_types (0, [])) in
  let arr_pseudo_kns : list kername :=
    List.map (fun '(_, nm) => (cur_mp, nm)) arr_name_pairs in
  let term_to_pkn (arr_t : term) : option kername :=
    match find (fun p => rfp_eqb_term (fst p) arr_t) arr_name_pairs with
    | Some (_, nm) => Some (cur_mp, nm)
    | None => None
    end in
  (* Cross-type dep edges as kn pairs (used in topo-sort). *)
  let a2i_pkn :=
    flat_map (fun e =>
      match term_to_pkn (fst e) with
      | Some pkn => [(pkn, snd e)] | None => [] end) all_a2i_edges in
  let i2a_pkn :=
    flat_map (fun e =>
      match term_to_pkn (snd e) with
      | Some pkn => [(fst e, pkn)] | None => [] end) i2a_edges in
  (* ── E: sigma2 pre-mappings ──────────────────────────────────────────── *)
  let pre_mapping :=
    List.map (fun kn => (kn, (cur_mp, snd kn ++ "'"))) type_kns in
  let pre_ind_mapping :=
    List.map (fun kn =>
      (kn, {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |}))
    type_kns in
  let pre_app_kn_mapping :=
    flat_map (fun e =>
      let head_kn     := fst (fst e) in
      let arg_terms_e := snd (fst e) in
      let spec_kn     := snd e in
      match find (fun p => eq_kername (fst p) spec_kn) pre_ind_mapping with
      | Some (_, lifted_ind) => [((head_kn, arg_terms_e), lifted_ind)]
      | None => []
      end) spec_kn_pairs in
  (* ── F: sigma2→sigma2 dep edges (mode-derived and spec-derived) ────── *)
  let plain_get_lifted_kns idx_ctx n_idx pos :=
    let snoc_p := n_idx - 1 - pos in
    match nth_error idx_ctx snoc_p with
    | None => []
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
      let input_kns :=
        dedup_kns (flat_map (plain_get_lifted_kns idx_ctx n_idx) in_pos) in
      flat_map (fun op =>
        flat_map (fun out_kn =>
          List.map (fun in_kn => (out_kn, in_kn))
            (filter (fun in_kn => negb (eq_kername in_kn out_kn)) input_kns))
        (plain_get_lifted_kns idx_ctx n_idx op))
      out_pos)
    modes_with_idx in
  (* ── H: quote sigma2 type bodies ────────────────────────────────────── *)
  type_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;; tmReturn (kn, mind)) type_kns ;;
  type_minds <- tmEval all type_minds ;;
  (* ── J and K: dead code — SCC detection is no longer needed now that L
     declares all lifted types in a single combined block. Kept for reference.

  (* ── J: compute sigma2 and arrow bodies for SCC detection ──────────── *)
  (* arr_term_mapping_pre: maps each arrow term to a pre-inductive so that
     tentative sigma2 bodies include extra ctors referencing arrow types,
     making sigma2→arrow deps visible for SCC analysis. *)
  let arr_term_mapping_pre :=
    List.map (fun '(arr_t, nm) =>
      (arr_t, {| inductive_mind := (cur_mp, nm); inductive_ind := 0 |}))
    arr_name_pairs in
  computed_bodies <- monad_fold_left (fun acc kn =>
    if existsb (eq_kername kn) arr_pseudo_kns then
      (* Arrow type: call lat_build_arrow_ind tentatively for SCC detection. *)
      match find (fun '(_, nm) => eq_kername (cur_mp, nm) kn) arr_name_pairs with
      | None => tmReturn acc
      | Some (arr_t, name) =>
        let body :=
          lat_build_arrow_ind arr_t name arr_name_pairs pre_ind_mapping
            fn_app_infos modes_with_idx cur_mp in
        tmReturn (List.app acc [(kn, body)])
      end
    else
      match find (fun p => eq_kername (fst p) kn) type_minds with
      | None => tmReturn acc
      | Some (_, old_mind) =>
        let pre_new_ind :=
          {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |} in
        let ext := filter (fun q => negb (eq_kername (fst q) kn)) pre_ind_mapping in
        let body :=
          make_lifted_mind old_mind kn pre_new_ind ext
            pre_app_kn_mapping spec_kn_pairs modes_with_idx fn_app_infos 1 0 true
            arr_term_mapping_pre in
        tmReturn (List.app acc [(kn, body)])
      end)
  combined_sorted [] ;;
  computed_bodies <- tmEval all computed_bodies ;;
  let new_kn_to_old :=
    List.map (fun p => (inductive_mind (snd p), fst p)) pre_ind_mapping in
  (* All dep edges from computed_bodies (sigma2↔sigma2, sigma2↔arrow, arrow↔sigma2, arrow↔arrow). *)
  let all_dep_edges :=
    flat_map (fun entry =>
      let self_kn  := fst entry in
      let body     := snd entry in
      let body_kns := collect_kns_from_mind body in
      flat_map (fun bkn =>
        match find (fun p => eq_kername (fst p) bkn) new_kn_to_old with
        | Some (_, old_kn) =>
          if eq_kername old_kn self_kn then []
          else if existsb (eq_kername old_kn) type_kns
               then [(self_kn, old_kn)]
               else []
        | None =>
          if andb (negb (eq_kername bkn self_kn))
                  (existsb (eq_kername bkn) arr_pseudo_kns)
          then [(self_kn, bkn)]
          else []
        end)
      body_kns)
    computed_bodies in
  (* ── K: SCCs over combined_kns (sigma2 + arrow) ────────────────────── *)
  let all_scc_edges_bidir :=
    filter (fun e =>
      existsb (fun e2 => andb (eq_kername (fst e2) (snd e))
                              (eq_kername (snd e2) (fst e)))
              all_dep_edges)
      all_dep_edges in
  let all_scc_groups :=
    group_connected_components combined_kns all_scc_edges_bidir in
  *)
  (* ── L: declare all lifted types in one combined mutual block ─────────── *)
  (* All sigma2 and arrow types are placed in a single tmMkInductive call,
     eliminating any ordering dependency between them. *)
  let all_sigma2_sorted := type_kns in
  let all_arrow_sorted := arr_pseudo_kns in
  let n_sigma2       := #|all_sigma2_sorted| in
  let n_arrow        := #|all_arrow_sorted| in
  let block_n_bodies := n_sigma2 + n_arrow in
  let first_kn_for_block :=
    match all_sigma2_sorted with
    | kn0 :: _ => kn0
    | [] => match all_arrow_sorted with kn0 :: _ => kn0 | [] => (cur_mp, "empty") end
    end in
  let block_kn := (cur_mp, snd first_kn_for_block ++ "'") in
  (* sigma2 kn → block inductive at index j *)
  let group_sigma2_mapping :=
    snd (fold_left (fun st kn_j =>
      let j := fst st in
      let a := snd st in
      (S j, List.app a [(kn_j, {| inductive_mind := block_kn; inductive_ind := j |})]))
    all_sigma2_sorted (0, [])) in
  (* arrow pseudo-kn → block inductive at index n_sigma2 + i *)
  let group_arrow_mapping :=
    snd (fold_left (fun st kn_j =>
      let i := fst st in
      let a := snd st in
      (S i, List.app a
        [(kn_j, {| inductive_mind := block_kn; inductive_ind := n_sigma2 + i |})]))
    all_arrow_sorted (0, [])) in
  let arr_term_mapping_block :=
    flat_map (fun p =>
      match find (fun q => eq_kername (fst q) (cur_mp, snd p)) group_arrow_mapping with
      | Some (_, arr_ind) => [(fst p, arr_ind)]
      | None => []
      end) arr_name_pairs in
  let grp_app_kn_mapping :=
    flat_map (fun e =>
      let spec_kn := snd e in
      match find (fun p => eq_kername (fst p) spec_kn) group_sigma2_mapping with
      | Some (_, grp_ind) => [(fst e, grp_ind)]
      | None => []
      end) spec_kn_pairs in
  (* Build sigma2 one_inductive_body values.
     ext_i for each kn_i = (all other sigma2 types) ++ (all arrow types),
     so every sibling type is available for substitution regardless of order. *)
  let sigma2_bodies :=
    snd (fold_left (fun st kn_i =>
      let block_body_offset := fst st in
      let bodies_so_far     := snd st in
      match find (fun p => eq_kername (fst p) kn_i) type_minds with
      | None => (S block_body_offset, bodies_so_far)
      | Some (_, old_mind_i) =>
        let pre_new_ind_i :=
          {| inductive_mind := block_kn; inductive_ind := block_body_offset |} in
        let ext_i :=
          List.app
            (filter (fun q => negb (eq_kername (fst q) kn_i)) group_sigma2_mapping)
            group_arrow_mapping in
        let m := make_lifted_mind old_mind_i kn_i pre_new_ind_i ext_i
                   grp_app_kn_mapping spec_kn_pairs modes_with_idx fn_app_infos
                   block_n_bodies block_body_offset true arr_term_mapping_block in
        (S block_body_offset, List.app bodies_so_far m.(ind_bodies))
      end)
    all_sigma2_sorted (0, [])) in
  (* Build arrow one_inductive_body values. *)
  let arrow_bodies :=
    flat_map (fun kn_a =>
      match find (fun '(_, nm) => eq_kername (cur_mp, nm) kn_a) arr_name_pairs with
      | None => []
      | Some (arr_t, name) =>
        let raw_mind :=
          lat_build_arrow_ind arr_t name arr_name_pairs group_sigma2_mapping
            fn_app_infos modes_with_idx cur_mp in
        let fix_cstr_args args :=
          mapi (fun snoc_i d =>
            let depth := #|args| - 1 - snoc_i in
            {| decl_name := d.(decl_name);
               decl_body := d.(decl_body);
               decl_type := subst_block_inds_to_rels block_kn block_n_bodies depth
                              d.(decl_type) |})
          args in
        let fix_cstr c :=
          {| cstr_name    := c.(cstr_name);
             cstr_args    := fix_cstr_args c.(cstr_args);
             cstr_indices := c.(cstr_indices);
             cstr_type    := subst_block_inds_to_rels block_kn block_n_bodies 0 c.(cstr_type);
             cstr_arity   := c.(cstr_arity) |} in
        match raw_mind.(ind_bodies) with
        | [oib] =>
          [{| ind_name      := oib.(ind_name);
              ind_indices   := oib.(ind_indices);
              ind_sort      := oib.(ind_sort);
              ind_type      := oib.(ind_type);
              ind_kelim     := oib.(ind_kelim);
              ind_ctors     := List.map fix_cstr oib.(ind_ctors);
              ind_projs     := oib.(ind_projs);
              ind_relevance := oib.(ind_relevance) |}]
        | _ => []
        end
      end)
    all_arrow_sorted in
  let all_bodies := List.app sigma2_bodies arrow_bodies in
  let block_universes :=
    match find (fun p => eq_kername (fst p) first_kn_for_block) type_minds with
    | Some (_, m) => m.(ind_universes) | None => Monomorphic_ctx end in
  let combined_body :=
    {| ind_finite    := Finite;
       ind_npars     := 0;
       ind_universes := block_universes;
       ind_variance  := None;
       ind_params    := [];
       ind_bodies    := all_bodies |} in
  combined_ev <- tmEval all combined_body ;;
  (if Nat.eqb (List.length all_bodies) 0 then tmReturn tt
   else tmMkInductivePreserveFinite combined_ev) ;;
  new_sigma2_inds <- monad_map (fun kn_i =>
    let short_nm := snd kn_i ++ "'" in
    refs <- tmLocate short_nm ;;
    let ai :=
      match find (fun g => match g with IndRef _ => true | _ => false end) refs with
      | Some (IndRef ind) => ind
      | _ => {| inductive_mind := block_kn; inductive_ind := 0 |}
      end in
    tmReturn (kn_i, ai))
  all_sigma2_sorted ;;
  new_arrow_inds <- monad_map (fun kn_a =>
    match find (fun '(_, nm) => eq_kername (cur_mp, nm) kn_a) arr_name_pairs with
    | None =>
      tmReturn (kn_a, {| inductive_mind := block_kn; inductive_ind := 0 |})
    | Some (_, name) =>
      refs <- tmLocate name ;;
      let ai :=
        match find (fun g => match g with IndRef _ => true | _ => false end) refs with
        | Some (IndRef ind) => ind
        | _ => {| inductive_mind := (cur_mp, name); inductive_ind := 0 |}
        end in
      tmReturn (kn_a, ai)
    end)
  all_arrow_sorted ;;
  let new_all_inds := List.app new_sigma2_inds new_arrow_inds in
  let result := (new_all_inds, List.map fst new_all_inds) in
  (* acc contains both sigma2 and arrow type entries (the latter were added so
     arr_term_mapping could find them in the declaration loop).  Strip arrow
     pseudo-kns before exposing actual_mapping so that downstream consumers
     (generate_push_params, generate_push_fns, etc.) only see sigma2 types. *)
  let actual_mapping :=
    filter (fun p => negb (existsb (eq_kername (fst p)) arr_pseudo_kns))
           (fst result) in
  actual_mapping <- tmEval all actual_mapping ;;
  (* ── M: build final return values ───────────────────────────────────── *)
  let final_app_kn_mapping :=
    flat_map (fun e =>
      let head_kn     := fst (fst e) in
      let arg_terms_e := snd (fst e) in
      let spec_kn     := snd e in
      match find (fun p => eq_kername (fst p) spec_kn) actual_mapping with
      | Some (_, lifted_ind) => [((head_kn, arg_terms_e), lifted_ind)]
      | None => []
      end) spec_kn_pairs in
  let final_lat_ind_mapping :=
    List.map (fun '(kn_i, ai) => (kn_i, inductive_mind ai)) actual_mapping in
  tmReturn (actual_mapping, final_app_kn_mapping, arr_name_pairs, final_lat_ind_mapping,
            modes_with_idx, fn_app_infos).
Set Universe Checking.

(* ------------------------------------------------------------------ *)
(** ** Combined preprocessing + lift-function generation              *)
(* ------------------------------------------------------------------ *)

(** Run [preprocess_all_lifting_types] and then [generate_lift_fns] in one
    call.  This is the entry point for testing: after it returns, the
    environment contains all lifted inductives (declared by
    [preprocess_all_lifting_types]) and a [<typeName>Lift] function for every
    sigma2 type in the lifting set (declared by [generate_lift_fns]).

    Parameters:
    - [modes]: mode map, same format as [preprocess_all_lifting_types]
    - [fuel]:  passed directly to [preprocess_all_lifting_types] for BFS
               expansion, and also used as the iteration bound for
               [compute_npi_fix] *)
Unset Universe Checking.

(** Declare [<name>Lift : arr_t -> <name>] for each arrow type.
    The body is [fun f => <name>LiftCstr f] — a plain lambda (no fixpoint).
    We use [tmLocate] on [<name>LiftCstr] to get the correct [inductive] and
    constructor index, because the arrow inductive is part of the combined
    sigma2+arrow mutual block — its kname is NOT [(cur_mp, name)]. *)
Polymorphic Fixpoint generate_arrow_lift_fns
    (arr_pairs : list (term * string))
    (cur_mp    : modpath)
    : TemplateMonad unit :=
  match arr_pairs with
  | [] => tmReturn tt
  | (arr_t, name) :: rest =>
    let anon_b := {| binder_name := nAnon; binder_relevance := Relevant |} in
    refs <- tmLocate (name ++ "LiftCstr") ;;
    match refs with
    | ConstructRef fn_ind cstr_idx :: _ =>
      let lift_body := tLambda anon_b arr_t
                        (tApp (tConstruct fn_ind cstr_idx []) [tRel 0]) in
      lift_ev <- tmEval all lift_body ;;
      tmMkDefinition (name ++ "Lift") lift_ev ;;
      generate_arrow_lift_fns rest cur_mp
    | _ =>
      tmMsg ("generate_arrow_lift_fns: constructor " ++ name ++ "LiftCstr not found") ;;
      generate_arrow_lift_fns rest cur_mp
    end
  end.

(* ------------------------------------------------------------------ *)
(** ** ChkNoExtraCstrs for the testing pathway                        *)
(* ------------------------------------------------------------------ *)

(** Build the [def term] for [<name>ChkNoExtraCstrs] for a lifted arrow-type
    inductive.  [fn_ind] is the lifted arrow inductive (obtained via [tmLocate]);
    [lift_cstr_idx] is the constructor index of [<name>LiftCstr] within
    [new_oib.(ind_ctors)].
    Returns [true] only for the [LiftCstr] constructor (a directly-lifted concrete
    function) and [false] for all other constructors (animation ctors and
    [<fnName>LiftedCstr] ctors).
    The function is wrapped in a [tFix] for uniformity with sigma2 ChkNoExtraCstrs,
    even though no recursion occurs (the LiftCstr arg has the original arrow type,
    not the lifted one). *)
Definition make_arrow_chk_def
    (name          : string)
    (fn_ind        : inductive)
    (lift_cstr_idx : nat)
    (new_oib       : one_inductive_body)
    : def term :=
  let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let new_t    := tInd fn_ind [] in
  let bool_ind := {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Corelib"], "bool");
                     inductive_ind  := 0 |} in
  let bool_t   := tInd bool_ind [] in
  let true_t   := tConstruct bool_ind 0 [] in
  let false_t  := tConstruct bool_ind 1 [] in
  let branches :=
    mapi (fun ctor_idx ctor =>
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := if Nat.eqb ctor_idx lift_cstr_idx then true_t else false_t |})
    new_oib.(ind_ctors) in
  let pred  := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := bool_t |} in
  let ci    := {| ci_ind := fn_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let dname := {| binder_name    := nNamed (name ++ "ChkNoExtraCstrs");
                  binder_relevance := Relevant |} in
  {| dname := dname;
     dtype  := tProd anon_b new_t bool_t;
     dbody  := tLambda anon_b new_t (tCase ci pred (tRel 0) branches);
     rarg   := 0 |}.

(** Declare [<name>ChkNoExtraCstrs : <name> -> bool] for each arrow type in
    [arr_pairs].  Uses [tmLocate] on [<name>LiftCstr] to discover the correct
    [inductive] and constructor index (the arrow inductive lives in the combined
    sigma2+arrow block, so its kname is NOT [(cur_mp, name)]). *)
Polymorphic Fixpoint generate_arrow_chk_fns
    (arr_pairs : list (term * string))
    (cur_mp    : modpath)
    : TemplateMonad unit :=
  match arr_pairs with
  | [] => tmReturn tt
  | (_, name) :: rest =>
    refs <- tmLocate (name ++ "LiftCstr") ;;
    match refs with
    | ConstructRef fn_ind lift_cstr_idx :: _ =>
      fn_mind <- tmQuoteInductive (inductive_mind fn_ind) ;;
      (match nth_error fn_mind.(ind_bodies) (inductive_ind fn_ind) with
      | None =>
        tmMsg ("generate_arrow_chk_fns: no body for " ++ name)
      | Some new_oib =>
        let d := make_arrow_chk_def name fn_ind lift_cstr_idx new_oib in
        chk_ev <- tmEval all (tFix [d] 0) ;;
        tmMkDefinition (name ++ "ChkNoExtraCstrs") chk_ev
      end) ;;
      generate_arrow_chk_fns rest cur_mp
    | _ =>
      tmMsg ("generate_arrow_chk_fns: constructor " ++ name ++ "LiftCstr not found") ;;
      generate_arrow_chk_fns rest cur_mp
    end
  end.

(** Like [generate_chk_fns] but finds the original body index by matching
    [ind_name] against [snd old_kn] rather than always using index 0.
    This is robust for multi-body mutual inductives (not currently produced by
    the pipeline, but correct in principle).
    Only generates functions for pi (purely-inductive) types in [pi_set]. *)
Polymorphic Fixpoint generate_chk_fns_robust
    (todo    : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map : list (kername * inductive))
    (pi_set  : list kername)
    (cur_mp  : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
    if negb (existsb (eq_kername old_kn) pi_set)
    then generate_chk_fns_robust rest all_map pi_set cur_mp
    else
      let orig_body_idx :=
        match find (fun p => String.eqb (snd p).(ind_name) (snd old_kn))
                   (mapi (fun i oib => (i, oib)) old_mind.(ind_bodies)) with
        | Some p => fst p
        | None   => 0
        end in
      tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
              | None =>
                tmFail ("generate_chk_fns_robust: no body for " ++ snd old_kn)
              | Some new_oib =>
                let n_old_ctors :=
                  match nth_error old_mind.(ind_bodies) orig_body_idx with
                  | Some ob => List.length ob.(ind_ctors)
                  | None    => 0
                  end in
                let n_block := List.length new_mind.(ind_bodies) in
                let d := make_chk_def old_kn new_ind n_block new_oib n_old_ctors all_map cur_mp in
                chk_term_ev <- tmEval all (tFix [d] 0) ;;
                tmMkDefinition (snd old_kn ++ "ChkNoExtraCstrs") chk_term_ev
              end) (fun _ =>
      generate_chk_fns_robust rest all_map pi_set cur_mp)
  end.

(** Generate [ChkNoExtraCstrs] functions for all types in the testing pathway.
    Handles both sigma2 types (from [type_mapping]) and arrow types (from
    [arr_name_pairs]).  Must be called after [generate_lift_fns] and
    [generate_arrow_lift_fns] so that all lifted inductives are in the environment.

    Sigma2 types are declared in topological dependency order: if A's constructors
    reference B then [BChkNoExtraCstrs] is declared before [AChkNoExtraCstrs].
    Arrow types need no ordering — [make_arrow_chk_def] only emits [true/false].

    Inputs are exactly those available inside [preprocess_and_generate_lifts]:
    - [type_mapping]   : sigma2 type map (original kn → new inductive)
    - [app_kn_mapping] : parametric specialisation map (for [pi_lift_deps])
    - [arr_name_pairs] : arrow type pairs (original arrow term × name)
    - [npi_set]        : non-purely-inductive kns (from [compute_npi_fix])
    - [cur_mp]         : current module path *)
Polymorphic Definition generate_chk_fns_testing
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (arr_name_pairs : list (term * string))
    (npi_set        : list kername)
    (cur_mp         : modpath)
    : TemplateMonad unit :=
  let pi_set :=
    List.map fst
      (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set)) type_mapping) in
  type_minds <- monad_map (fun '(old_kn, new_ind) =>
    old_mind <- tmQuoteInductive old_kn ;;
    new_mind <- tmQuoteInductive (inductive_mind new_ind) ;;
    tmReturn ((old_kn, new_ind), (old_mind, new_mind)))
    type_mapping ;;
  type_minds <- tmEval all type_minds ;;
  (* Topo-sort pi entries: AChkNoExtraCstrs references BChkNoExtraCstrs whenever
     A's constructors mention B — same dep graph as pi lift fns, so pi_lift_deps
     applies directly.  npi entries are filtered out first (generate_chk_fns_robust
     skips them, but we exclude them here so the sorted list only has pi types). *)
  let pi_minds :=
    filter (fun '((old_kn, _), _) => existsb (eq_kername old_kn) pi_set) type_minds in
  let pi_sort_inputs :=
    List.map (fun '((old_kn, new_ind), (old_mind, _)) =>
      let orig_body_idx :=
        match find (fun p => String.eqb (snd p).(ind_name) (snd old_kn))
                   (mapi (fun i oib => (i, oib)) old_mind.(ind_bodies)) with
        | Some p => fst p
        | None   => 0
        end in
      let deps :=
        match nth_error old_mind.(ind_bodies) orig_body_idx with
        | Some oib => pi_lift_deps old_kn oib type_mapping app_kn_mapping pi_set
        | None     => []
        end in
      (old_kn, new_ind, deps))
    pi_minds in
  let sorted_pi := topo_sort_pi pi_sort_inputs [] (S (List.length pi_sort_inputs)) in
  let sorted_pi_minds :=
    flat_map (fun '(old_kn, _) =>
      match find (fun '((kn, _), _) => eq_kername kn old_kn) pi_minds with
      | Some entry => [entry]
      | None       => []
      end)
    sorted_pi in
  _ <- generate_chk_fns_robust sorted_pi_minds type_mapping pi_set cur_mp ;;
  generate_arrow_chk_fns arr_name_pairs cur_mp.

(* ------------------------------------------------------------------ *)
(** ** PushPlain for the testing pathway                               *)
(* ------------------------------------------------------------------ *)

(** Declare [undefined<name> : arr_t] (if not already present) and then
    [<name>PushPlain : <name> -> arr_t] for each arrow type in [arr_pairs].
    Uses [tmLocate] on [<name>LiftCstr] to discover the correct [inductive]
    and constructor index robustly (the arrow inductive lives in the combined
    sigma2+arrow block, so its kname is NOT [(cur_mp, name)]).
    For the [LiftCstr] branch: extract and return the inner [arr_t] value.
    For all other branches: return [undefined<name>]. *)
Polymorphic Fixpoint generate_arrow_push_fns
    (arr_pairs : list (term * string))
    (cur_mp    : modpath)
    : TemplateMonad unit :=
  match arr_pairs with
  | [] => tmReturn tt
  | (arr_t, name) :: rest =>
    let anon_b    := {| binder_name := nAnon; binder_relevance := Relevant |} in
    let undef_nm  := "undefined" ++ name in
    let undef_ref := tConst (cur_mp, undef_nm) [] in
    tmMkParameter undef_nm arr_t ;;
    refs <- tmLocate (name ++ "LiftCstr") ;;
    match refs with
    | ConstructRef fn_ind lift_cstr_idx :: _ =>
      fn_mind <- tmQuoteInductive (inductive_mind fn_ind) ;;
      (match nth_error fn_mind.(ind_bodies) (inductive_ind fn_ind) with
      | None =>
        tmMsg ("generate_arrow_push_fns: no body for " ++ name)
      | Some new_oib =>
        let fn_type    := tInd fn_ind [] in
        let ci_plain   := {| ci_ind := fn_ind; ci_npar := 0; ci_relevance := Relevant |} in
        let pred_plain := {| puinst := []; pparams := []; pcontext := [anon_b];
                             preturn := arr_t |} in
        let branches :=
          mapi (fun i ctor =>
            let n_args := ctor.(cstr_arity) in
            if Nat.eqb i lift_cstr_idx then
              {| bcontext := [anon_b]; bbody := tRel 0 |}
            else
              {| bcontext := List.map (fun _ => anon_b) (seq 0 n_args);
                 bbody    := undef_ref |})
          new_oib.(ind_ctors) in
        let push_body :=
          tLambda anon_b fn_type (tCase ci_plain pred_plain (tRel 0) branches) in
        push_ev <- tmEval all push_body ;;
        tmMkDefinition (name ++ "PushPlain") push_ev
      end) ;;
      generate_arrow_push_fns rest cur_mp
    | _ =>
      tmMsg ("generate_arrow_push_fns: constructor " ++ name ++ "LiftCstr not found") ;;
      generate_arrow_push_fns rest cur_mp
    end
  end.

(** Like [generate_push_fns_plain] but:
    - Finds the original body index by matching [ind_name] against [snd old_kn]
      rather than always using index 0 (robust for multi-body mutual inductives).
    - Always passes [is_purely_ind = true]: only pi types appear in the testing
      pathway, so no fuel parameter is needed.
    - Skips any entry not in [pi_set]. *)
Polymorphic Fixpoint generate_push_fns_robust
    (todo       : list ((kername * inductive) * (mutual_inductive_body * mutual_inductive_body)))
    (all_map    : list (kername * inductive))
    (app_kn_map : list (kername * list term * inductive))
    (pi_set     : list kername)
    (cur_mp     : modpath)
    : TemplateMonad unit :=
  match todo with
  | [] => tmReturn tt
  | ((old_kn, new_ind), (old_mind, new_mind)) :: rest =>
    if negb (existsb (eq_kername old_kn) pi_set)
    then generate_push_fns_robust rest all_map app_kn_map pi_set cur_mp
    else
      let orig_body_idx :=
        match find (fun p => String.eqb (snd p).(ind_name) (snd old_kn))
                   (mapi (fun i oib => (i, oib)) old_mind.(ind_bodies)) with
        | Some p => fst p
        | None   => 0
        end in
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
      tmMkParameter ("undefined" ++ snd old_kn) old_type ;;
      tmBind (match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
              | None =>
                tmFail ("generate_push_fns_robust: no body for " ++ snd old_kn)
              | Some new_oib =>
                let n_old_ctors :=
                  match nth_error old_mind.(ind_bodies) orig_body_idx with
                  | Some ob => List.length ob.(ind_ctors)
                  | None    => 0
                  end in
                let n_block := List.length new_mind.(ind_bodies) in
                let d := make_push_def_plain old_kn new_ind n_block new_oib n_old_ctors
                                             all_map app_kn_map pi_set true cur_mp in
                push_term_ev <- tmEval all (tFix [d] 0) ;;
                tmMkDefinition (snd old_kn ++ "PushPlain") push_term_ev
              end) (fun _ =>
      generate_push_fns_robust rest all_map app_kn_map pi_set cur_mp)
  end.

(** Generate [PushPlain] functions for all types in the testing pathway.
    Handles both sigma2 types (from [type_mapping]) and arrow types (from
    [arr_name_pairs]).  Must be called after [generate_lift_fns] and
    [generate_arrow_lift_fns] so that all lifted inductives are in the environment.

    Sigma2 types are declared in topological dependency order matching
    [generate_chk_fns_testing]: if A's constructors reference B then
    [BPushPlain] is declared before [APushPlain].

    Arrow type [PushPlain] functions have no cross-type references (the
    [LiftCstr] argument has the original arrow type), so ordering is
    irrelevant for them.

    Inputs are the same as [generate_chk_fns_testing]. *)
Polymorphic Definition generate_push_fns_testing
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (arr_name_pairs : list (term * string))
    (npi_set        : list kername)
    (cur_mp         : modpath)
    : TemplateMonad unit :=
  let pi_set :=
    List.map fst
      (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set)) type_mapping) in
  type_minds <- monad_map (fun '(old_kn, new_ind) =>
    old_mind <- tmQuoteInductive old_kn ;;
    new_mind <- tmQuoteInductive (inductive_mind new_ind) ;;
    tmReturn ((old_kn, new_ind), (old_mind, new_mind)))
    type_mapping ;;
  type_minds <- tmEval all type_minds ;;
  let pi_minds :=
    filter (fun '((old_kn, _), _) => existsb (eq_kername old_kn) pi_set) type_minds in
  let pi_sort_inputs :=
    List.map (fun '((old_kn, new_ind), (old_mind, _)) =>
      let orig_body_idx :=
        match find (fun p => String.eqb (snd p).(ind_name) (snd old_kn))
                   (mapi (fun i oib => (i, oib)) old_mind.(ind_bodies)) with
        | Some p => fst p
        | None   => 0
        end in
      let deps :=
        match nth_error old_mind.(ind_bodies) orig_body_idx with
        | Some oib => pi_lift_deps old_kn oib type_mapping app_kn_mapping pi_set
        | None     => []
        end in
      (old_kn, new_ind, deps))
    pi_minds in
  let sorted_pi := topo_sort_pi pi_sort_inputs [] (S (List.length pi_sort_inputs)) in
  let sorted_pi_minds :=
    flat_map (fun '(old_kn, _) =>
      match find (fun '((kn, _), _) => eq_kername kn old_kn) pi_minds with
      | Some entry => [entry]
      | None       => []
      end)
    sorted_pi in
  _ <- generate_push_fns_robust sorted_pi_minds type_mapping app_kn_mapping pi_set cur_mp ;;
  generate_arrow_push_fns arr_name_pairs cur_mp.

Polymorphic Definition preprocess_and_generate_lifts
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad (list (kername * inductive)
                   * list (kername * list term * inductive)
                   * list (term * string)
                   * list kername) :=
  cur_mp  <- tmCurrentModPath tt ;;
  preproc <- preprocess_all_lifting_types modes fuel ;;
  let '(((((type_mapping, app_kn_mapping), arr_name_pairs),
           _lat_ind_mapping), _modes_with_idx), _fn_app_infos) := preproc in
  npi_set <- compute_npi_fix type_mapping ([] : list kername) (List.length type_mapping + 1) ;;
  npi_set <- tmEval all npi_set ;;
  generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp true npi_set ;;
  generate_arrow_lift_fns arr_name_pairs cur_mp ;;
  tmReturn (type_mapping, app_kn_mapping, arr_name_pairs, npi_set).

Polymorphic Definition preprocess_and_generate_lifts_and_chkFns
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad unit :=
  cur_mp <- tmCurrentModPath tt ;;
  '(type_mapping, app_kn_mapping, arr_name_pairs, npi_set) <-
      preprocess_and_generate_lifts modes fuel ;;
  generate_chk_fns_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp.

(** Full testing-pathway entry point: preprocesses, declares lifted inductives,
    then generates [Lift], [ChkNoExtraCstrs], and [PushPlain] functions for
    every type in the lifting set (both sigma2 and arrow types).
    Equivalent to calling [preprocess_and_generate_lifts_and_chkFns] followed
    by [generate_push_fns_testing] with the same intermediate data. *)
Polymorphic Definition preprocess_and_generate_all
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad unit :=
  cur_mp <- tmCurrentModPath tt ;;
  '(type_mapping, app_kn_mapping, arr_name_pairs, npi_set) <-
      preprocess_and_generate_lifts modes fuel ;;
  generate_chk_fns_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp ;;
  generate_push_fns_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp.

(* ------------------------------------------------------------------ *)
(** ** TransparentSigmaPush for the testing pathway                   *)
(* ------------------------------------------------------------------ *)

(** Compute TransparentSigmaPush topo-sort deps by scanning ALL constructor
    args (original + animation) of [new_oib].  Returns the deduplicated list
    of sigma2 old-kernnames and arrow pseudo-kernnames that must be processed
    before this type.  [all_pi_set] should contain both sigma2 old-kernames
    (from [pi_set]) and arrow pseudo-knames [(cur_mp, name)] so that arrow
    types are treated as deps when they appear as ctor args. *)
Definition compute_transp_push_deps
    (new_kn        : kername)
    (n_block       : nat)
    (body_idx      : nat)
    (new_oib       : one_inductive_body)
    (type_map      : list (kername * inductive))
    (arr_name_pairs: list (term * string))
    (all_pi_set    : list kername)
    (cur_mp        : modpath)
    : list kername :=
  List.fold_left
    (fun acc kn => if existsb (eq_kername kn) acc then acc else List.app acc [kn])
    (List.flat_map (fun ctor =>
       let n_args := ctor.(cstr_arity) in
       List.flat_map (fun snoc_i =>
         let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                      | Some d => d.(decl_type) | None => tVar "?" end in
         match push_arg_class new_kn n_block body_idx type_map n_args snoc_i arg_t with
         | Some (Some kn) =>
           if existsb (eq_kername kn) all_pi_set then [kn] else []
         | _ =>
           match arg_t with
           | tInd ind _ =>
             let arg_kn := inductive_mind ind in
             match find (fun e => eq_kername (cur_mp, snd e) arg_kn) arr_name_pairs with
             | Some (_, nm) =>
               let arr_kn := (cur_mp, nm) in
               if existsb (eq_kername arr_kn) all_pi_set then [arr_kn] else []
             | None => []
             end
           | _ => []
           end
         end)
       (seq 0 n_args))
     new_oib.(ind_ctors))
    [].

(** Build the body [def term] for [nameTransparentSigmaPushBody] of an arrow
    type, using [arr_t] as the return type.  Animation ctors apply their
    [Symb_unwrap] hole to pushed args; sigma2-typed args call their
    [TransparentSigmaPushBody] with hole refs from [pi_set_holes]. *)
Definition make_arrow_transparent_push_body_def
    (arr_t           : term)
    (name            : string)
    (fn_ind          : inductive)
    (new_oib         : one_inductive_body)
    (n_block         : nat)
    (arr_name_pairs  : list (term * string))
    (type_mapping    : list (kername * inductive))
    (unique_ht_terms : list term)
    (pi_set_holes    : list (kername * list term))
    (cur_mp          : modpath)
    : def term :=
  let fn_kn      := inductive_mind fn_ind in
  let anon_b     := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let new_type   := tInd fn_ind [] in
  let n_holes    := List.length unique_ht_terms in
  let s_hole_ref := fun (n_args k : nat) => tRel (n_args + n_holes - k) in
  let all_holes  := fun (n_args : nat) =>
    List.map (fun k => s_hole_ref n_args k) (seq 0 n_holes) in
  let s_fix_ref  := fun (n_args : nat) => tRel (n_args + n_holes + 1) in
  let lift_nm    := name ++ "LiftCstr" in
  let push_one_arg := fun (n_args snoc_i : nat) (arg_t : term) =>
    let depth := n_args - 1 - snoc_i in
    match arg_t with
    | tRel n =>
      if andb (Nat.leb depth n) (Nat.ltb (n - depth) 1)
      then tApp (s_fix_ref n_args) (List.app (all_holes n_args) [tRel snoc_i])
      else tRel snoc_i
    | tInd ind _ =>
      let arg_kn := inductive_mind ind in
      if eq_kername arg_kn fn_kn then
        tApp (s_fix_ref n_args) (List.app (all_holes n_args) [tRel snoc_i])
      else
        match find (fun e => eq_kername (cur_mp, snd e) arg_kn) arr_name_pairs with
        | Some _ =>
          tApp (tConst (cur_mp, snd arg_kn ++ "TransparentSigmaPushBody") []) [tRel snoc_i]
        | None =>
          match find (fun e => eq_kername (inductive_mind (snd e)) arg_kn) type_mapping with
          | Some (old_kn, _) =>
            let kn_hs :=
              match find (fun e => eq_kername (fst e) old_kn) pi_set_holes with
              | Some (_, hs) => hs | None => [] end in
            let kn_h_refs :=
              List.map (fun h_t =>
                match h_t with
                | tInd hind _ =>
                  s_hole_ref n_args
                    (find_hole_idx_by_kn (inductive_mind hind) unique_ht_terms)
                | _ => tVar "hole_not_found"
                end) kn_hs in
            tApp (tConst (cur_mp, snd old_kn ++ "TransparentSigmaPushBody") [])
                 (List.app kn_h_refs [tRel snoc_i])
          | None => tRel snoc_i
          end
        end
    | _ => tRel snoc_i
    end in
  let branches :=
    mapi (fun _ ctor =>
      let ctor_nm := ctor.(cstr_name) in
      let n_args  := ctor.(cstr_arity) in
      let bbody :=
        if String.eqb ctor_nm lift_nm then tRel 0
        else
          let pushed_snoc :=
            List.map (fun snoc_i =>
              let arg_t := match nth_error ctor.(cstr_args) snoc_i with
                           | Some d => d.(decl_type) | None => tVar "?" end in
              push_one_arg n_args snoc_i arg_t)
            (seq 0 n_args) in
          let pushed := List.rev pushed_snoc in
          if string_is_suffix ctor_nm "LiftedCstr" then
            let fn_nm  := string_take (string_len ctor_nm - 10) ctor_nm in
            let fn_ref := tConst (cur_mp, fn_nm) [] in
            match pushed with [] => fn_ref | _ => tApp fn_ref pushed end
          else
            let w_kn := (cur_mp, ctor_nm ++ "Symb") in
            match find (fun h => match h with
                                 | tInd ind _ => eq_kername (inductive_mind ind) w_kn
                                 | _ => false
                                 end) unique_ht_terms with
            | Some _ =>
              let w_idx  := find_hole_idx_by_kn w_kn unique_ht_terms in
              let fn_ref :=
                tApp (tConst (cur_mp, ctor_nm ++ "Symb_unwrap") []) [s_hole_ref n_args w_idx] in
              match pushed with [] => fn_ref | _ => tApp fn_ref pushed end
            | None => tVar ("unknown_arrow_ctor_" ++ ctor_nm)
            end
      in
      {| bcontext := List.rev (List.map (fun d => d.(decl_name)) ctor.(cstr_args));
         bbody    := bbody |})
    new_oib.(ind_ctors) in
  let body_pred := {| puinst := []; pparams := []; pcontext := [anon_b]; preturn := arr_t |} in
  let body_ci   := {| ci_ind := fn_ind; ci_npar := 0; ci_relevance := Relevant |} in
  let d_nm      := {| binder_name := nNamed (name ++ "TransparentSigmaPushBody");
                      binder_relevance := Relevant |} in
  let base_dtype := tProd anon_b new_type arr_t in
  let dtype     :=
    List.fold_right (fun h_t acc => tProd anon_b h_t acc) base_dtype unique_ht_terms in
  let dbody     :=
    List.fold_right (fun h_t acc => tLambda anon_b h_t acc)
      (tLambda anon_b new_type (tCase body_ci body_pred (tRel 0) branches))
      unique_ht_terms in
  {| dname := d_nm; dtype := dtype; dbody := dbody; rarg := n_holes |}.

(** Build the wrapper [<name>TransparentSigmaPush : <name> -> HoleyResult arr_t]
    by folding [hr_pure]/[hr_ap]/[hr_hole] over the hole list.  Uses [arr_t]
    directly (not [subst_ind_to_old]) so it works for arrow types. *)
Definition make_arrow_transp_push_wrapper
    (name            : string)
    (fn_ind          : inductive)
    (arr_t           : term)
    (unique_ht_terms : list term)
    (hr_pure_c hr_ap_c hr_hole_c : term)
    (cur_mp          : modpath)
    : term :=
  let anon_b    := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let new_type  := tInd fn_ind [] in
  let body_c    := tConst (cur_mp, name ++ "TransparentSigmaPushBody") [] in
  let n_holes   := List.length unique_ht_terms in
  let hole_args := List.map (fun k => tRel (n_holes - 1 - k)) (seq 0 n_holes) in
  let s_ref     := tRel n_holes in
  let body_call := tApp body_c (List.app hole_args [s_ref]) in
  let inner_fn  :=
    List.fold_right (fun h_t acc => tLambda anon_b h_t acc) body_call unique_ht_terms in
  let b_type_chain :=
    List.fold_right
      (fun h_t acc => tProd anon_b h_t (List.hd arr_t acc) :: acc)
      [arr_t] unique_ht_terms in
  let init_hr   := tApp hr_pure_c [List.hd arr_t b_type_chain; inner_fn] in
  let '(_, final_hr) :=
    List.fold_left
      (fun '(b_tail, cur_hr) h_t =>
        let b_cur := List.hd arr_t b_tail in
        (List.tl b_tail, tApp hr_ap_c [h_t; b_cur; cur_hr; tApp hr_hole_c [h_t]]))
      unique_ht_terms (List.tl b_type_chain, init_hr) in
  tLambda anon_b new_type final_hr.

(** Generate [AnSymb] wrapper inductives and unwrap functions for the animation
    constructors of each sigma2 type in [sigma2_data].  Uses robust [n_old_ctors]
    (already computed via name-based body lookup). *)
Polymorphic Fixpoint generate_sigma2_transp_symb_wrappers
    (sigma2_data    : list (kername * inductive * one_inductive_body * nat * nat * nat))
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (cur_mp         : modpath)
    : TemplateMonad unit :=
  match sigma2_data with
  | [] => tmReturn tt
  | (old_kn, new_ind, new_oib, n_old_ctors, n_block, n_params) :: rest =>
    let type_nm := snd old_kn in
    let extra   := List.skipn n_old_ctors new_oib.(ind_ctors) in
    let extra   :=
      filter (fun c => negb (String.eqb c.(cstr_name) (type_nm ++ "LiftCstr"))) extra in
    let extra   :=
      filter (fun c => negb (string_is_suffix c.(cstr_name) "LiftedCstr")) extra in
    _ <- List.fold_left
      (fun acc_m c =>
        acc_m ;;
        let fn_type :=
          make_fnSymb_type new_ind n_block n_params c type_mapping app_kn_mapping in
        fn_type_ev <- tmEval all fn_type ;;
        let wrapper_nm := c.(cstr_name) ++ "Symb" in
        let body := make_wrapper_inductive_body wrapper_nm fn_type_ev in
        body_ev  <- tmEval all body ;;
        let W_ind := {| inductive_mind := (cur_mp, wrapper_nm); inductive_ind := 0 |} in
        let unwrap_body := build_unwrap_fn W_ind fn_type_ev in
        unwrap_ev <- tmEval all unwrap_body ;;
        _ <- tmMkInductive' body_ev ;;
        tmMkDefinition (wrapper_nm ++ "_unwrap") unwrap_ev)
      extra (tmReturn tt) ;;
    generate_sigma2_transp_symb_wrappers rest type_mapping app_kn_mapping cur_mp
  end.

(** Generate [AnSymb] wrapper inductives and unwrap functions for the animation
    constructors of each arrow type in [arr_data].  Uses [lat_unlift_type] to
    recover original argument types, with [tRel _] → [arr_t] fallback. *)
Polymorphic Fixpoint generate_arrow_transp_symb_wrappers
    (arr_data       : list (term * string * inductive * nat * one_inductive_body * nat * nat))
    (arr_name_pairs : list (term * string))
    (ind_mapping    : list (kername * kername))
    (cur_mp         : modpath)
    : TemplateMonad unit :=
  match arr_data with
  | [] => tmReturn tt
  | (arr_t, _, fn_ind, lift_cstr_idx, new_oib, _, _) :: rest =>
    let anon_b     := {| binder_name := nAnon; binder_relevance := Relevant |} in
    let unlift_t   := lat_unlift_type arr_name_pairs ind_mapping cur_mp in
    let anim_ctors := List.firstn lift_cstr_idx new_oib.(ind_ctors) in
    _ <- List.fold_left
      (fun acc_m ctor =>
        acc_m ;;
        let orig_arg_type_of d :=
          let t := unlift_t d.(decl_type) in
          match t with tRel _ => arr_t | _ => t end in
        let orig_arg_types := List.rev (List.map orig_arg_type_of ctor.(cstr_args)) in
        let fn_type :=
          List.fold_right (fun ty acc => tProd anon_b ty acc) arr_t orig_arg_types in
        fn_type_ev <- tmEval all fn_type ;;
        let wrapper_nm := ctor.(cstr_name) ++ "Symb" in
        let body := make_wrapper_inductive_body wrapper_nm fn_type_ev in
        body_ev  <- tmEval all body ;;
        let W_ind := {| inductive_mind := (cur_mp, wrapper_nm); inductive_ind := 0 |} in
        let unwrap_body := build_unwrap_fn W_ind fn_type_ev in
        unwrap_ev <- tmEval all unwrap_body ;;
        _ <- tmMkInductive' body_ev ;;
        tmMkDefinition (wrapper_nm ++ "_unwrap") unwrap_ev)
      anim_ctors (tmReturn tt) ;;
    generate_arrow_transp_symb_wrappers rest arr_name_pairs ind_mapping cur_mp
  end.

(** Generate [<Name>TransparentSigmaPushBody] and [<Name>TransparentSigmaPush]
    in topological order, accumulating [pi_set_holes] as each type is processed.
    Dispatches on whether each sorted entry belongs to sigma2 or arrow data. *)
Polymorphic Fixpoint generate_transp_push_in_order
    (sorted         : list (kername * inductive))
    (sigma2_data    : list (kername * inductive * one_inductive_body * nat * nat * nat))
    (arr_data       : list (term * string * inductive * nat * one_inductive_body * nat * nat))
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (arr_name_pairs : list (term * string))
    (pi_set         : list kername)
    (cur_mp         : modpath)
    (hr_hole_c hr_pure_c hr_ap_c : term)
    (pi_set_holes   : list (kername * list term))
    : TemplateMonad (list (kername * list term)) :=
  match sorted with
  | [] => tmReturn pi_set_holes
  | (kn, _) :: rest =>
    let recurse := fun new_ph =>
      generate_transp_push_in_order rest sigma2_data arr_data
        type_mapping app_kn_mapping arr_name_pairs pi_set cur_mp
        hr_hole_c hr_pure_c hr_ap_c (pi_set_holes ++ [new_ph]) in
    match find (fun e =>
                  let '(old_kn, _, _, _, _, _) := e in eq_kername old_kn kn)
               sigma2_data with
    | Some entry =>
      let '(old_kn, new_ind, new_oib, n_old_ctors, n_block, _) := entry in
      let '(unique_ht_terms, _) :=
        compute_push_unique_holes old_kn new_ind n_block new_oib n_old_ctors
          type_mapping pi_set true true cur_mp pi_set_holes arr_name_pairs in
      let d_body :=
        make_transparent_sigma_push_body_def
          old_kn new_ind n_block new_oib n_old_ctors
          type_mapping app_kn_mapping pi_set true cur_mp
          unique_ht_terms pi_set_holes true [] arr_name_pairs in
      body_ev <- tmEval all (tFix [d_body] 0) ;;
      _ <- tmMkDefinition (snd old_kn ++ "TransparentSigmaPushBody") body_ev ;;
      wrapper_ev <- tmEval all
        (make_transparent_sigma_push_wrapper_term
           old_kn new_ind type_mapping app_kn_mapping true cur_mp
           unique_ht_terms hr_pure_c hr_ap_c hr_hole_c) ;;
      _ <- tmMkDefinition (snd old_kn ++ "TransparentSigmaPush") wrapper_ev ;;
      recurse (old_kn, unique_ht_terms)
    | None =>
      match find (fun e =>
                    let '(_, nm, _, _, _, _, _) := e in eq_kername (cur_mp, nm) kn)
                 arr_data with
      | Some entry =>
        let '(arr_t, name, fn_ind, _, new_oib, n_block, _) := entry in
        let arr_kn := (cur_mp, name) in
        let '(unique_ht_terms, _) :=
          compute_push_unique_holes arr_kn fn_ind n_block new_oib 0
            type_mapping pi_set true true cur_mp pi_set_holes arr_name_pairs in
        let d_body :=
          make_arrow_transparent_push_body_def
            arr_t name fn_ind new_oib n_block arr_name_pairs type_mapping
            unique_ht_terms pi_set_holes cur_mp in
        body_ev <- tmEval all (tFix [d_body] 0) ;;
        _ <- tmMkDefinition (name ++ "TransparentSigmaPushBody") body_ev ;;
        wrapper_ev <- tmEval all
          (make_arrow_transp_push_wrapper name fn_ind arr_t
             unique_ht_terms hr_pure_c hr_ap_c hr_hole_c cur_mp) ;;
        _ <- tmMkDefinition (name ++ "TransparentSigmaPush") wrapper_ev ;;
        recurse (arr_kn, unique_ht_terms)
      | None =>
        generate_transp_push_in_order rest sigma2_data arr_data
          type_mapping app_kn_mapping arr_name_pairs pi_set cur_mp
          hr_hole_c hr_pure_c hr_ap_c pi_set_holes
      end
    end
  end.

(** Generate [TransparentSigmaPush] functions for all types in the testing
    pathway.  Declares [AnSymb] wrapper inductives for animation constructors,
    then declares [<Name>TransparentSigmaPushBody] and [<Name>TransparentSigmaPush]
    in topological order derived from ALL constructor args (original + animation).
    Handles both sigma2 and arrow types; no [PushPlain] calls anywhere. *)
Polymorphic Definition generate_transparent_push_testing
    (type_mapping   : list (kername * inductive))
    (app_kn_mapping : list (kername * list term * inductive))
    (arr_name_pairs : list (term * string))
    (npi_set        : list kername)
    (cur_mp         : modpath)
    : TemplateMonad unit :=
  let pi_set :=
    List.map fst
      (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set)) type_mapping) in
  hr_hole_tm <- tmQuote hr_hole ;;
  hr_pure_tm <- tmQuote hr_pure ;;
  hr_ap_tm   <- tmQuote hr_ap ;;
  sigma2_raw <- monad_map (fun '(old_kn, new_ind) =>
    old_mind <- tmQuoteInductive old_kn ;;
    new_mind <- tmQuoteInductive (inductive_mind new_ind) ;;
    tmReturn ((old_kn, new_ind), (old_mind, new_mind)))
    type_mapping ;;
  sigma2_raw <- tmEval all sigma2_raw ;;
  let sigma2_data :=
    flat_map (fun '((old_kn, new_ind), (old_mind, new_mind)) =>
      let orig_body_idx :=
        match find (fun p => String.eqb (snd p).(ind_name) (snd old_kn))
                   (mapi (fun i oib => (i, oib)) old_mind.(ind_bodies)) with
        | Some p => fst p | None => 0
        end in
      let n_old_ctors :=
        match nth_error old_mind.(ind_bodies) orig_body_idx with
        | Some ob => List.length ob.(ind_ctors) | None => 0
        end in
      let n_block  := List.length new_mind.(ind_bodies) in
      let n_params := new_mind.(ind_npars) in
      match nth_error new_mind.(ind_bodies) (inductive_ind new_ind) with
      | Some new_oib => [(old_kn, new_ind, new_oib, n_old_ctors, n_block, n_params)]
      | None         => []
      end)
    sigma2_raw in
  arr_raw <- monad_map (fun '(arr_t, name) =>
    refs <- tmLocate (name ++ "LiftCstr") ;;
    match refs with
    | ConstructRef fn_ind lift_cstr_idx :: _ =>
      fn_mind <- tmQuoteInductive (inductive_mind fn_ind) ;;
      tmReturn (Some (arr_t, name, fn_ind, lift_cstr_idx, fn_mind))
    | _ =>
      tmMsg ("generate_transparent_push_testing: " ++ name ++ "LiftCstr not found") ;;
      tmReturn None
    end)
    arr_name_pairs ;;
  arr_raw <- tmEval all arr_raw ;;
  let arr_data :=
    flat_map (fun opt =>
      match opt with
      | None => []
      | Some (arr_t, name, fn_ind, lift_cstr_idx, fn_mind) =>
        let n_block  := List.length fn_mind.(ind_bodies) in
        let n_params := fn_mind.(ind_npars) in
        match nth_error fn_mind.(ind_bodies) (inductive_ind fn_ind) with
        | Some new_oib => [(arr_t, name, fn_ind, lift_cstr_idx, new_oib, n_block, n_params)]
        | None         => []
        end
      end)
    arr_raw in
  _ <- generate_sigma2_transp_symb_wrappers sigma2_data type_mapping app_kn_mapping cur_mp ;;
  let ind_mapping :=
    List.map (fun '(old_kn, new_ind) => (old_kn, inductive_mind new_ind)) type_mapping in
  _ <- generate_arrow_transp_symb_wrappers arr_data arr_name_pairs ind_mapping cur_mp ;;
  (* Combined pi_set: sigma2 old-kernames + arrow pseudo-kernames (cur_mp, name). *)
  let arr_pseudo_kns :=
    List.map (fun '(_, name, _, _, _, _, _) => (cur_mp, name)) arr_data in
  let all_pi_set := List.app pi_set arr_pseudo_kns in
  let sigma2_sort_inputs :=
    List.map (fun '(old_kn, new_ind, new_oib, _, n_block, _) =>
      let body_idx := inductive_ind new_ind in
      let new_kn   := inductive_mind new_ind in
      let deps :=
        compute_transp_push_deps new_kn n_block body_idx new_oib
          type_mapping arr_name_pairs all_pi_set cur_mp in
      (old_kn, new_ind, deps))
    sigma2_data in
  let arr_sort_inputs :=
    List.map (fun '(_, name, fn_ind, _, new_oib, n_block, _) =>
      let body_idx := inductive_ind fn_ind in
      let new_kn   := inductive_mind fn_ind in
      let deps :=
        compute_transp_push_deps new_kn n_block body_idx new_oib
          type_mapping arr_name_pairs all_pi_set cur_mp in
      ((cur_mp, name), fn_ind, deps))
    arr_data in
  let all_sort_inputs := List.app sigma2_sort_inputs arr_sort_inputs in
  let sorted := topo_sort_pi all_sort_inputs [] (S (List.length all_sort_inputs)) in
  _ <- generate_transp_push_in_order sorted sigma2_data arr_data
    type_mapping app_kn_mapping arr_name_pairs pi_set cur_mp
    hr_hole_tm hr_pure_tm hr_ap_tm [] ;;
  tmReturn tt.

(** Full testing-pathway entry point: preprocesses, generates lifted types,
    Lift/ChkNoExtraCstrs/PushPlain/TransparentSigmaPush functions for all
    types in the lifting set (both sigma2 and arrow types). *)
Polymorphic Definition preprocess_and_generate_all_with_transparent_push
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad unit :=
  cur_mp <- tmCurrentModPath tt ;;
  '(type_mapping, app_kn_mapping, arr_name_pairs, npi_set) <-
      preprocess_and_generate_lifts modes fuel ;;
  generate_chk_fns_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp ;;
  generate_push_fns_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp ;;
  generate_transparent_push_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp.

(** Like [preprocess_and_generate_all_with_transparent_push] but returns the
    intermediate data so that callers can use it for subsequent pipeline steps
    (liftedFuncs, relation lifting, inputLift, outputPush, eqFn). *)
Polymorphic Definition preprocess_and_generate_all_with_transparent_push_data
    (modes : mode_map)
    (fuel  : nat)
    : TemplateMonad (list (kername * inductive)
                   * list (kername * list term * inductive)
                   * list (term * string)
                   * list kername
                   * list fn_app_info
                   * list lat_ind_pair
                   * list mode_with_idx) :=
  cur_mp <- tmCurrentModPath tt ;;
  preproc <- preprocess_all_lifting_types modes fuel ;;
  let '(((((type_mapping, app_kn_mapping), arr_name_pairs),
           lat_ind_mapping), modes_with_idx), fn_app_infos) := preproc in
  npi_set <- compute_npi_fix type_mapping ([] : list kername) (List.length type_mapping + 1) ;;
  npi_set <- tmEval all npi_set ;;
  generate_lift_fns type_mapping type_mapping app_kn_mapping cur_mp true npi_set ;;
  generate_arrow_lift_fns arr_name_pairs cur_mp ;;
  generate_chk_fns_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp ;;
  generate_push_fns_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp ;;
  generate_transparent_push_testing type_mapping app_kn_mapping arr_name_pairs npi_set cur_mp ;;
  tmReturn (type_mapping, app_kn_mapping, arr_name_pairs, npi_set, fn_app_infos,
            lat_ind_mapping, modes_with_idx).

Set Universe Checking.


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
     evalCmd vs (Assign v e) (set vs v (evalExp vs e))
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

MetaRocq Run (preprocess_and_generate_all
  [("evalCmd", ([0;1], [2]))] 500).
Print cmdPushPlain. 

 
Print natChkNoExtraCstrs.
Print cmdLift.  
End ImpSem.  
  
Module StackStep.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.



Definition eqFnsinstr (t1 t2 : sinstr) : bool :=
  true.

Definition stack := list nat.
Definition prog  := list sinstr.

Definition appSt (st : string -> nat) (s : string) : nat := st s.



Inductive stack_step : (string -> nat) -> list sinstr -> list nat -> list sinstr -> list nat -> Prop :=
| SS_Push  : forall st stk n p,
     stack_step st (SPush n :: p) stk p (n :: stk) 
| SS_Load  : forall st stk i p,
     
     stack_step (st) (SLoad i :: p)  stk p ((appSt st i) :: stk) 
   
| SS_Plus  : forall st stk n m p, stack_step st (SPlus :: p) (n :: m :: stk) p ((m + n) :: stk)
| SS_Minus : forall st stk n m p,
    stack_step st (SMinus :: p) (n :: m :: stk) p  ((m - n) :: stk)
| SS_Mult  : forall st stk n m p,
    stack_step st (SMult :: p) (n :: m :: stk) p  ((m * n) :: stk).
    
MetaRocq Run (preprocess_and_generate_all
  [("stack_step", ([0;1;2], [3;4]))] 500 ).
  
Print fnType0PushPlain.
Print listnatPushPlain.  
  

Print listsinstrChkNoExtraCstrs.  


  
End StackStep.

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
  
MetaRocq Run (preprocess_and_generate_all
  [("bigStepTr", ([0], [1]));("step", ([0], [1]))] 500). 
Print tmPushPlain.
Print coLstLift.   
  
End bigStepTr.

(** Collect named constants that appear as standalone [tConst kn] references —
    i.e. NOT as the immediate head of a [tApp].  Used to find function-valued
    constants (e.g. extracted lambdas [fnLamK]) that need simple Lift lifting. *)
Fixpoint collect_standalone_fn_kns_from_term (t : term) : list kername :=
  match t with
  | tConst kn _ => [kn]
  | tApp f args =>
    let head_hits :=
      match f with
      | tConst _ _ => []  (* in application position — do NOT collect *)
      | _          => collect_standalone_fn_kns_from_term f
      end in
    List.app head_hits (flat_map collect_standalone_fn_kns_from_term args)
  | tProd _ ty body =>
    List.app (collect_standalone_fn_kns_from_term ty)
             (collect_standalone_fn_kns_from_term body)
  | tLambda _ ty body =>
    List.app (collect_standalone_fn_kns_from_term ty)
             (collect_standalone_fn_kns_from_term body)
  | tLetIn _ val ty body =>
    List.app (collect_standalone_fn_kns_from_term val)
    (List.app (collect_standalone_fn_kns_from_term ty)
              (collect_standalone_fn_kns_from_term body))
  | tCase _ _ disc branches =>
    List.app (collect_standalone_fn_kns_from_term disc)
    (flat_map (fun br => collect_standalone_fn_kns_from_term br.(bbody)) branches)
  | _ => []
  end.

Definition collect_standalone_fn_kns_from_ctor (c : constructor_body) : list kername :=
  List.app
    (flat_map (fun d => collect_standalone_fn_kns_from_term d.(decl_type)) c.(cstr_args))
  (List.app
    (collect_standalone_fn_kns_from_term c.(cstr_type))
    (flat_map collect_standalone_fn_kns_from_term c.(cstr_indices))).

(** Declare push/lift functions for one lifted arrow type [name] (e.g. [fnType0]).
    Assumes the [Inductive name] has already been declared.  Produces (in order):
      [undefined<name>]                    Parameter of type [arr_t]
      [<name>Lift]                         fun f => <name>LiftCstr f
      [<name>PushPlain]                    case: LiftCstr → inner; else → undefined
      [<ctor>Symb] / [<ctor>Symb_unwrap]   one wrapper inductive per animation ctor
      [<name>TransparentSigmaPushBody]     fix with rarg = n_holes
      [<name>TransparentSigmaPush]         hr_pure/hr_ap wrapper                     *)
Unset Universe Checking.
(** Steps C, D, D2 are delegated to the testing-path generators
    (generate_arrow_lift_fns, generate_arrow_push_fns, generate_arrow_chk_fns).
    Steps E, F, G (Symb wrappers + TransparentSigmaPushBody + TransparentSigmaPush)
    are built inline using the same logic as the testing path. *)
Polymorphic Definition generate_arrow_type_fns
    (arr_t           : term)
    (name            : string)
    (arr_name_pairs  : list (term * string))
    (ind_mapping     : list (kername * kername))
    (fn_app_infos    : list (kername * list term * term))
    (cur_mp          : modpath)
    (hr_hole_c hr_pure_c hr_ap_c : term)
    (pi_set          : list kername)
    (pi_set_holes_in : list (kername * list term))
    : TemplateMonad unit :=
  (* Steps C, D, D2: Lift, PushPlain (+ undefined<name>), ChkNoExtraCstrs. *)
  generate_arrow_lift_fns [(arr_t, name)] cur_mp ;;
  generate_arrow_push_fns [(arr_t, name)] cur_mp ;;
  generate_arrow_chk_fns  [(arr_t, name)] cur_mp ;;
  (* Steps E, F, G: Symb wrappers + TransparentSigmaPushBody + TransparentSigmaPush
     via the testing-path functions generate_arrow_transp_symb_wrappers and
     generate_transp_push_in_order. *)
  let type_mapping_approx :=
    List.map (fun '(old_kn, new_kn) =>
      (old_kn, {| inductive_mind := new_kn; inductive_ind := 0 |}))
    ind_mapping in
  refs <- tmLocate (name ++ "LiftCstr") ;;
  match refs with
  | ConstructRef fn_ind lift_cstr_idx :: _ =>
    fn_mind <- tmQuoteInductive (inductive_mind fn_ind) ;;
    let n_block  := List.length fn_mind.(ind_bodies) in
    let n_params := fn_mind.(ind_npars) in
    (match nth_error fn_mind.(ind_bodies) (inductive_ind fn_ind) with
    | None => tmMsg ("generate_arrow_type_fns: no body for " ++ name)
    | Some new_oib =>
      let arr_data :=
        [(arr_t, name, fn_ind, lift_cstr_idx, new_oib, n_block, n_params)] in
      _ <- generate_arrow_transp_symb_wrappers
             arr_data arr_name_pairs ind_mapping cur_mp ;;
      _ <- generate_transp_push_in_order
             [((cur_mp, name), fn_ind)] [] arr_data
             type_mapping_approx [] arr_name_pairs pi_set cur_mp
             hr_hole_c hr_pure_c hr_ap_c pi_set_holes_in ;;
      tmReturn tt
    end)
  | _ =>
    tmMsg ("generate_arrow_type_fns: constructor " ++ name ++ "LiftCstr not found")
  end.
Set Universe Checking.

(** Declare [liftedFunc] (full check/push/apply/lift) for named functions that
    appear as the HEAD of a [tApp] with an arrow return type, and
    [liftedFuncVal] (simple Lift wrapping) for standalone named function
    constants whose TYPE is a lifted arrow type.
    A function appearing in both positions gets both definitions.
    [fn_app_infos]   : functions in application positions (full procedure).
    [standalone_kns] : standalone function kernel names (simple procedure). *)
Unset Universe Checking.
Polymorphic Definition generate_arrow_liftedFuncs
    (fn_app_infos   : list (kername * list term * term))
    (standalone_kns : list kername)
    (arr_name_pairs : list (term * string))
    (ind_mapping    : list (kername * kername))
    (cur_mp         : modpath)
    : TemplateMonad unit :=
  let anon_b   := {| binder_name := nAnon; binder_relevance := Relevant |} in
  let bool_ind := {| inductive_mind :=
                       (MPfile ["Datatypes"; "Init"; "Corelib"], "bool");
                     inductive_ind := 0 |} in
  let bool_type := tInd bool_ind [] in
  let true_t    := tConstruct bool_ind 0 [] in
  let andb_kn   := (MPfile ["Datatypes"; "Init"; "Corelib"], "andb") in
  let fold_andb chks :=
    match chks with
    | []  => true_t
    | [c] => c
    | _   => List.fold_right (fun c acc => tApp (tConst andb_kn []) [c; acc]) true_t chks
    end in
  (* Classify an argument/return type term.
     Returns [Some (inl nm)]         if it's a lifted arrow type named nm.
     Returns [Some (inr (ok, nk))]   if it's a lifted inductive (old kn, new kn).
     Returns [None]                  if it's a regular/unlifted type. *)
  let resolve_tp := fun (tp : term) =>
    match find (fun p => rfp_eqb_term (fst p) tp) arr_name_pairs with
    | Some (_, nm) => Some (inl nm)
    | None =>
      match tp with
      | tInd ind _ =>
        let kn := inductive_mind ind in
        match find (fun p => eq_kername (fst p) kn) ind_mapping with
        | Some p => Some (inr p)
        | None   => None
        end
      | _ => None
      end
    end in
  (* Part 1: full [liftedFunc] for functions in application positions. *)
  monad_map (fun '((fn_kn, arg_types), ret_type) =>
    match find (fun p => rfp_eqb_term (fst p) ret_type) arr_name_pairs with
    | None => tmReturn tt
    | Some (_, ret_nm) =>
      let ret_ind_t := tInd {| inductive_mind := (cur_mp, ret_nm); inductive_ind := 0 |} [] in
      let n := List.length arg_types in
      let arg_infos := List.map resolve_tp arg_types in
      let lifted_arg_types :=
        List.map (fun '(info, tp) =>
          match info with
          | Some (inl nm) => tInd {| inductive_mind := (cur_mp, nm); inductive_ind := 0 |} []
          | Some (inr (_, new_kn)) => tInd {| inductive_mind := new_kn; inductive_ind := 0 |} []
          | None => tp
          end) (combine arg_infos arg_types) in
      let chk_terms :=
        flat_map (fun '(i, info) =>
          let rel_i := tRel (n - 1 - i) in
          match info with
          | Some (inl nm) =>
            [tApp (tConst (cur_mp, nm ++ "ChkNoExtraCstrs") []) [rel_i]]
          | Some (inr (old_kn, _)) =>
            [tApp (tConst (cur_mp, snd old_kn ++ "ChkNoExtraCstrs") []) [rel_i]]
          | None => []
          end) (mapi (fun i info => (i, info)) arg_infos) in
      let all_good := fold_andb chk_terms in
      let pushed_args :=
        mapi (fun i info =>
          let rel_i := tRel (n - 1 - i) in
          match info with
          | Some (inl nm) =>
            tApp (tConst (cur_mp, nm ++ "PushPlain") []) [rel_i]
          | Some (inr (old_kn, _)) =>
            tApp (tConst (cur_mp, snd old_kn ++ "PushPlain") []) [rel_i]
          | None => rel_i
          end) arg_infos in
      let f_applied :=
        match pushed_args with
        | [] => tConst fn_kn []
        | _  => tApp (tConst fn_kn []) pushed_args
        end in
      let lifted_out := tApp (tConst (cur_mp, ret_nm ++ "Lift") []) [f_applied] in
      (* undef_out must have the lifted type (ret_ind_t), not the raw arr_t *)
      let undef_out  := tApp (tConst (cur_mp, ret_nm ++ "Lift") [])
                             [tConst (cur_mp, "undefined" ++ ret_nm) []] in
      let bool_ci    := {| ci_ind := bool_ind; ci_npar := 0; ci_relevance := Relevant |} in
      let bool_pred  := {| puinst := []; pparams := []; pcontext := [anon_b];
                           preturn := ret_ind_t |} in
      let body :=
        if Nat.eqb (List.length chk_terms) 0 then
          lifted_out
        else
          tCase bool_ci bool_pred all_good
            [{| bcontext := []; bbody := lifted_out |};
             {| bcontext := []; bbody := undef_out  |}] in
      let fn_term :=
        List.fold_right (fun tp acc => tLambda anon_b tp acc) body lifted_arg_types in
      fn_term_ev <- tmEval all fn_term ;;
      tmMkDefinition (snd fn_kn ++ "liftedFunc") fn_term_ev
    end)
  fn_app_infos ;;
  (* Part 2: simple [liftedFuncVal] for standalone function constants. *)
  monad_map (fun fn_kn =>
    cb <- tmQuoteConstant fn_kn false ;;
    let fn_ty := cb.(cst_type) in
    match find (fun p => rfp_eqb_term (fst p) fn_ty) arr_name_pairs with
    | None => tmReturn tt
    | Some (_, nm) =>
      let val_term := tApp (tConst (cur_mp, nm ++ "Lift") []) [tConst fn_kn []] in
      val_ev <- tmEval all val_term ;;
      tmMkDefinition (snd fn_kn ++ "liftedFuncVal") val_ev
    end)
  standalone_kns ;;
  tmReturn tt.
Set Universe Checking.

(** Steps 2–8 of the arrow-type lifting pipeline (everything after
    [remove_from_fn_pos] has already been called).
    [ind_mapping] : old_kn → new_kn for already-lifted inductives so that
    An-constructor input types in [lat_build_arrow_ind] are lifted correctly. *)
Unset Universe Checking.
Polymorphic Definition declare_arrow_types_for_relation
    (top_kn     : kername)
    (modes      : mode_map)
    (ind_mapping : list (kername * kername))
    (fuel       : nat)
    : TemplateMonad unit :=
  (* Step 2: build mode map over the removeFnPos relation names. *)
  let modes_rfp :=
    List.map (fun '(nm, io) => (nm ++ "removeFnPos", io)) modes in
  (* Step 3: compute the arrow-type lifting set from removeFnPos relations. *)
  r <- compute_lifted_arrow_types modes_rfp [] fuel ;;
  let arrow_types := fst r in
  if Nat.eqb #|arrow_types| 0 then tmReturn tt
  else
  cur_mp <- tmCurrentModPath tt ;;
  (* Step 4: re-quote removeFnPos relations to obtain modes_with_idx and
     fn_app_infos for constructor building (mirrors steps 1-4 of
     compute_lifted_arrow_types, applied to modes_rfp). *)
  rel_inds <- monad_map (fun p =>
    refs <- tmLocate (fst p) ;;
    match find (fun g =>
        match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("lift_arrow_types_for_relation: cannot locate '" ++ fst p ++ "'")
    end) modes_rfp ;;
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;;
    tmReturn (kn, mind)) rel_block_kns ;;
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => [] | Some oib => oib.(ind_indices)
          end
        end in
      ((fst mode_e, snd mode_e), idx_ctx))
    (combine modes_rfp rel_inds) in
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
    rel_block_minds) [] in
  let extra_fn_pairs :=
    fold_left (fun acc p =>
      let fn_kn := fst p in
      if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) fn_app_infos_base)
             (existsb (fun q => eq_kername (fst q) fn_kn) acc)
      then acc else List.app acc [p])
    (flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds) [] in
  extra_fn_infos <- monad_map (fun p =>
    let fn_kn := fst p in
    let n     := List.length (snd p) in
    cb <- tmQuoteConstant fn_kn false ;;
    let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
    tmReturn (fn_kn, decl_arg_types, ret_tp)) extra_fn_pairs ;;
  let fn_app_infos := List.app fn_app_infos_base extra_fn_infos in
  (* Step 5: assign sequential names fnType0, fnType1, ... to the arrow types. *)
  let arr_name_pairs : list (term * string) :=
    snd (fold_left (fun '(i, acc) t =>
      (S i, List.app acc [(t, "fnType" ++ string_of_nat i)]))
    arrow_types (0, [])) in
  (* Step 6: build and declare one Inductive per lifted arrow type. *)
  monad_map (fun '(arr_t, name) =>
    let ind_mapping_inductive :=
      List.map (fun '(kn, new_kn) =>
        (kn, {| inductive_mind := new_kn; inductive_ind := 0 |}))
      ind_mapping in
    let mind := lat_build_arrow_ind arr_t name arr_name_pairs ind_mapping_inductive
                  fn_app_infos modes_with_idx cur_mp in
    tmMkInductivePreserveFinite mind)
  arr_name_pairs ;;
  tmReturn tt.
  (* Steps 7-8 are in generate_arrow_fns_for_relation — call that after sigma2
     push functions have been generated (which steps 7+ may reference). *)
Set Universe Checking.

(** Steps 7–8 of the arrow-type lifting pipeline: generate functions for the
    already-declared fnTypeN inductives.  Sigma2 push functions (e.g.
    [cmdPushPlain]) must have been declared before calling this, because
    [generate_arrow_type_fns] generates [TransparentSigmaPushBody] bodies that
    reference them.  Steps 2–5 are recomputed (read-only quotation). *)
Unset Universe Checking.
Polymorphic Definition generate_arrow_fns_for_relation
    (top_kn      : kername)
    (modes       : mode_map)
    (ind_mapping : list (kername * kername))
    (fuel        : nat)
    : TemplateMonad unit :=
  let modes_rfp :=
    List.map (fun '(nm, io) => (nm ++ "removeFnPos", io)) modes in
  r <- compute_lifted_arrow_types modes_rfp [] fuel ;;
  let arrow_types := fst r in
  if Nat.eqb #|arrow_types| 0 then tmReturn tt
  else
  cur_mp <- tmCurrentModPath tt ;;
  rel_inds <- monad_map (fun p =>
    refs <- tmLocate (fst p) ;;
    match find (fun g =>
        match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("generate_arrow_fns_for_relation: cannot locate '" ++ fst p ++ "'")
    end) modes_rfp ;;
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;;
    tmReturn (kn, mind)) rel_block_kns ;;
  let modes_with_idx :=
    List.map (fun mi =>
      let mode_e  := fst mi in
      let rel_ind := snd mi in
      let kn      := inductive_mind rel_ind in
      let bidx    := inductive_ind  rel_ind in
      let idx_ctx :=
        match find (fun p => eq_kername (fst p) kn) rel_block_minds with
        | None => []
        | Some (_, mind) =>
          match nth_error mind.(ind_bodies) bidx with
          | None => [] | Some oib => oib.(ind_indices)
          end
        end in
      ((fst mode_e, snd mode_e), idx_ctx))
    (combine modes_rfp rel_inds) in
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
    rel_block_minds) [] in
  let extra_fn_pairs :=
    fold_left (fun acc p =>
      let fn_kn := fst p in
      if orb (existsb (fun e => eq_kername (fst (fst e)) fn_kn) fn_app_infos_base)
             (existsb (fun q => eq_kername (fst q) fn_kn) acc)
      then acc else List.app acc [p])
    (flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_const_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds) [] in
  extra_fn_infos <- monad_map (fun p =>
    let fn_kn := fst p in
    let n     := List.length (snd p) in
    cb <- tmQuoteConstant fn_kn false ;;
    let '(decl_arg_types, ret_tp) := fn_info_from_cst_type n cb.(cst_type) in
    tmReturn (fn_kn, decl_arg_types, ret_tp)) extra_fn_pairs ;;
  let fn_app_infos := List.app fn_app_infos_base extra_fn_infos in
  let arr_name_pairs : list (term * string) :=
    snd (fold_left (fun '(i, acc) t =>
      (S i, List.app acc [(t, "fnType" ++ string_of_nat i)]))
    arrow_types (0, [])) in
  (* Step 7: declare push/lift/chk/symb functions for each lifted arrow type. *)
  hr_hole_tm <- tmQuote (hr_hole) ;;
  hr_pure_tm <- tmQuote (hr_pure) ;;
  hr_ap_tm   <- tmQuote (hr_ap)   ;;
  let type_mapping_approx :=
    List.map (fun '(old_kn, new_kn) =>
      (old_kn, {| inductive_mind := new_kn; inductive_ind := 0 |}))
    ind_mapping in
  npi_set_loc <- compute_npi_fix type_mapping_approx [] (List.length type_mapping_approx + 1) ;;
  npi_set_loc <- tmEval all npi_set_loc ;;
  let pi_set_loc :=
    List.map fst
      (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set_loc)) type_mapping_approx) in
  monad_map (fun '(arr_t, name) =>
    generate_arrow_type_fns arr_t name arr_name_pairs ind_mapping fn_app_infos
      cur_mp hr_hole_tm hr_pure_tm hr_ap_tm pi_set_loc [])
  arr_name_pairs ;;
  (* Step 8: collect standalone function constants and declare liftedFuncs. *)
  let standalone_kns_raw :=
    dedup_kns (flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_standalone_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds) in
  let standalone_kns :=
    filter (fun kn =>
      negb (existsb (fun e => eq_kername (fst (fst e)) kn) fn_app_infos))
    standalone_kns_raw in
  generate_arrow_liftedFuncs fn_app_infos standalone_kns arr_name_pairs ind_mapping cur_mp ;;
  tmReturn tt.
Set Universe Checking.

(** Steps 7–8 of the arrow-type pipeline with pre-computed [arr_name_pairs]
    and [fn_app_infos] from [preprocess_all_lifting_types].  [modes_rfp] is
    still needed to locate the inductive blocks for standalone-fn scanning. *)
Unset Universe Checking.
Polymorphic Definition generate_arrow_fns_pre
    (modes_rfp      : mode_map)
    (arr_name_pairs : list (term * string))
    (fn_app_infos   : list (kername * list term * term))
    (ind_mapping    : list (kername * kername))
    : TemplateMonad unit :=
  if Nat.eqb #|arr_name_pairs| 0 then tmReturn tt
  else
  cur_mp <- tmCurrentModPath tt ;;
  rel_inds <- monad_map (fun p =>
    refs <- tmLocate (fst p) ;;
    match find (fun g =>
        match g with IndRef _ | ConstructRef _ _ => true | _ => false end) refs with
    | Some (IndRef ind)         => tmReturn ind
    | Some (ConstructRef ind _) => tmReturn ind
    | _ => tmFail ("generate_arrow_fns_pre: cannot locate '" ++ fst p ++ "'")
    end) modes_rfp ;;
  let rel_block_kns := dedup_kns (List.map inductive_mind rel_inds) in
  rel_block_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;;
    tmReturn (kn, mind)) rel_block_kns ;;
  hr_hole_tm <- tmQuote (hr_hole) ;;
  hr_pure_tm <- tmQuote (hr_pure) ;;
  hr_ap_tm   <- tmQuote (hr_ap)   ;;
  let type_mapping_approx :=
    List.map (fun '(old_kn, new_kn) =>
      (old_kn, {| inductive_mind := new_kn; inductive_ind := 0 |}))
    ind_mapping in
  npi_set_loc <- compute_npi_fix type_mapping_approx [] (List.length type_mapping_approx + 1) ;;
  npi_set_loc <- tmEval all npi_set_loc ;;
  let pi_set_loc :=
    List.map fst
      (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set_loc)) type_mapping_approx) in
  monad_map (fun '(arr_t, name) =>
    generate_arrow_type_fns arr_t name arr_name_pairs ind_mapping fn_app_infos
      cur_mp hr_hole_tm hr_pure_tm hr_ap_tm pi_set_loc [])
  arr_name_pairs ;;
  let standalone_kns_raw :=
    dedup_kns (flat_map (fun km =>
      flat_map (fun oib =>
        flat_map collect_standalone_fn_kns_from_ctor oib.(ind_ctors))
      (snd km).(ind_bodies))
    rel_block_minds) in
  let standalone_kns :=
    filter (fun kn =>
      negb (existsb (fun e => eq_kername (fst (fst e)) kn) fn_app_infos))
    standalone_kns_raw in
  generate_arrow_liftedFuncs fn_app_infos standalone_kns arr_name_pairs ind_mapping cur_mp ;;
  tmReturn tt.
Set Universe Checking.

(** Full pipeline: remove function positions then declare fnTypeN.
    Calls [remove_from_fn_pos] first, then [declare_arrow_types_for_relation].
    Pass [ind_mapping=[]] when the inductive lifting has not been done yet;
    the An-constructor input types will then be unlifted. *)
Unset Universe Checking.
Polymorphic Definition lift_arrow_types_for_relation
    (top_kn      : kername)
    (modes       : mode_map)
    (ind_mapping : list (kername * kername))
    (fuel        : nat)
    : TemplateMonad unit :=
  remove_from_fn_pos top_kn modes ;;
  declare_arrow_types_for_relation top_kn modes ind_mapping fuel ;;
  generate_arrow_fns_for_relation top_kn modes ind_mapping fuel.
Set Universe Checking.

(** Full animation pipeline for relations with arrow-type parameters.
    Uses [preprocess_and_generate_all_with_transparent_push_data] to run the
    testing-path preprocessing (Lift, ChkNoExtraCstrs, PushPlain, AnSymb
    wrappers, TransparentSigmaPush), then generates eqFn, liftedFuncs (sigma2
    + arrow), lifts the relation, generates inputLift/outputPush using the
    testing-pipeline functions by name, animates the lifted relation, and
    assembles [top_rel_nm ++ "TransparentSigma2AnimatedTopFn"]. *)
Unset Universe Checking.
Polymorphic Definition animate_coinductive_with_fn_pos
    (top_kn : kername)
    (modes  : mode_map)
    (fuel   : nat)
    : TemplateMonad unit :=
  let top_rel_nm := snd top_kn in
  remove_from_fn_pos top_kn modes ;;
  let modes_rfp :=
    List.map (fun '(nm, io) => (nm ++ "removeFnPos", io)) modes in
  let rfp_rel_nm := top_rel_nm ++ "removeFnPos" in
  kn_mode_list <- monad_fold_left (fun acc me =>
    refs <- tmLocate (fst me) ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [(ind, me)])
    | _ => tmFail ("animate_coinductive_with_fn_pos: cannot find '" ++ fst me ++ "'")
    end)
    modes_rfp [] ;;
  match kn_mode_list return TemplateMonad unit with
  | [] => @tmFail unit "animate_coinductive_with_fn_pos: no modes provided"
  | _  =>
    cur_mp <- tmCurrentModPath tt ;;
    '(type_mapping, app_kn_mapping, arr_name_pairs, npi_set,
      fn_app_infos_rfp, lat_ind_mapping, modes_with_idx_rfp) <-
        preprocess_and_generate_all_with_transparent_push_data modes_rfp fuel ;;
    let arr_subst : list (term * term) :=
      List.map (fun '(arr_t, nm) =>
        (arr_t, tInd {| inductive_mind := (cur_mp, nm); inductive_ind := 0 |} []))
      arr_name_pairs in
    let pi_set :=
      List.map fst (filter (fun e => negb (existsb (eq_kername (fst e)) npi_set)) type_mapping) in
    type_minds <- monad_map (fun entry =>
      old_mind <- tmQuoteInductive (fst entry) ;;
      new_mind <- tmQuoteInductive (inductive_mind (snd entry)) ;;
      tmReturn (entry, (old_mind, new_mind)))
      type_mapping ;;
    type_minds <- tmEval all type_minds ;;
    prod_refs <- tmLocate "prod" ;;
    anim_refs <- tmLocate "animation_result" ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) prod_refs,
          find (fun g => match g with IndRef _ => true | _ => false end) anim_refs with
    | Some (IndRef prod_ind), Some (IndRef anim_ind) =>
      let prod_kn     := inductive_mind prod_ind in
      let anim_res_kn := inductive_mind anim_ind in
      _ <- generate_eqfn_defs type_minds type_mapping pi_set cur_mp ;;
      let unique_fn_infos := fn_app_infos_rfp in
      _ <- generate_lifted_fns unique_fn_infos type_mapping app_kn_mapping cur_mp arr_name_pairs ;;
      let fn_kn_map :=
        List.map (fun fi => (fst (fst fi), (cur_mp, snd (fst (fst fi)) ++ "liftedFunc")))
                 unique_fn_infos in
      let unique_block_kns :=
        fold_left (fun acc p =>
          if existsb (eq_kername (inductive_mind (fst p))) acc then acc
          else List.app acc [inductive_mind (fst p)])
        kn_mode_list [] in
      let rel_mapping :=
        List.map (fun kn =>
          (kn, {| inductive_mind := (cur_mp, snd kn ++ "'"); inductive_ind := 0 |}))
          unique_block_kns in
      rel_block_minds_assoc <- monad_map (fun kn =>
        mind <- tmQuoteInductive kn ;;
        tmReturn (kn, mind))
        unique_block_kns ;;
      rel_block_minds_assoc <- tmEval all rel_block_minds_assoc ;;
      let standalone_kns_raw :=
        dedup_kns (flat_map (fun km =>
          flat_map (fun oib =>
            flat_map collect_standalone_fn_kns_from_ctor oib.(ind_ctors))
          (snd km).(ind_bodies))
        rel_block_minds_assoc) in
      let standalone_kns :=
        filter (fun kn =>
          negb (existsb (fun e => eq_kername (fst (fst e)) kn) unique_fn_infos))
        standalone_kns_raw in
      _ <- generate_arrow_liftedFuncs unique_fn_infos standalone_kns arr_name_pairs lat_ind_mapping cur_mp ;;
      let block_id_map := List.map (fun kn => (kn, kn)) unique_block_kns in
      let sorted_block_kns :=
        topo_sort_kns unique_block_kns rel_block_minds_assoc block_id_map
                      [] [] (S #|unique_block_kns|) in
      _ <- monad_fold_left (fun _ block_kn =>
        let block_mwi :=
          filter (fun mwi =>
            let nm := fst (fst mwi) in
            existsb (fun p =>
              andb (String.eqb (fst (snd p)) nm)
                   (eq_kername (inductive_mind (fst p)) block_kn))
            kn_mode_list)
          modes_with_idx_rfp in
        lift_relation_mwi block_kn rel_mapping type_mapping app_kn_mapping block_mwi fn_kn_map arr_subst true)
        sorted_block_kns tt ;;
      _ <- generate_inputLift_fns kn_mode_list type_mapping app_kn_mapping
                                   prod_kn anim_res_kn cur_mp true npi_set arr_name_pairs ;;
      _ <- generate_rest_fns kn_mode_list cur_mp prod_kn ;;
      hr_type_tm <- tmQuote (HoleyResult) ;;
      hr_pair_tm <- tmQuote (hr_pair) ;;
      hr_pure_tm <- tmQuote (hr_pure) ;;
      let pi_set_all := List.map fst type_mapping in
      _ <- generate_transparent_sigma_outputPush_fns kn_mode_list type_mapping app_kn_mapping pi_set_all
                              arr_name_pairs prod_kn anim_res_kn cur_mp hr_type_tm hr_pair_tm hr_pure_tm ;;
      let rfp_block_kn := List.hd (cur_mp, "") unique_block_kns in
      let lifted_kn    := (cur_mp, snd rfp_block_kn ++ "'") in
      let lifted_modes := List.map (fun me => (fst me ++ "'", snd me)) modes_rfp in
      _ <- animate_coinductive lifted_kn lifted_modes fuel ;;
      rfp_mind <- tmQuoteInductive rfp_block_kn ;;
      match find (fun me => String.eqb (fst me) rfp_rel_nm) modes_rfp,
            find (fun ob => String.eqb ob.(ind_name) rfp_rel_nm) rfp_mind.(ind_bodies) with
      | Some (_, (in_pos, out_pos)), Some rfp_oib =>
        let n_params  := rfp_mind.(ind_npars) in
        let n_total   := List.length in_pos + List.length out_pos in
        let all_types := extract_arg_types n_params n_total rfp_oib.(ind_type) in
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
          let inputLift_fn            := tConst (cur_mp, rfp_rel_nm ++ "inputLift") [] in
          let transparentSigmaPush_fn := tConst (cur_mp, rfp_rel_nm ++ "TransparentSigmaOutputPush") [] in
          let animFn                  := tConst (cur_mp, rfp_rel_nm ++ "'" ++ top_fn_suffix) [] in
          let composite :=
            tLambda anon_b (tInd nat_ind [])
            (tLambda anon_b anim_in_type
            (tApp transparentSigmaPush_fn
              [tRel 1;
               tApp animFn [tRel 1; tApp inputLift_fn [tRel 1; tRel 0]]]))
          in
          let unlift_arr := lat_unlift_type arr_name_pairs lat_ind_mapping cur_mp in
          arr_an_hole_infos_raw <- monad_map (fun '(arr_t, nm) =>
            let fn_kn  := (cur_mp, nm) in
            let fn_ind := {| inductive_mind := fn_kn; inductive_ind := 0 |} in
            arr_mind <- tmQuoteInductive fn_kn ;;
            let ctors :=
              match nth_error arr_mind.(ind_bodies) 0 with
              | Some oib => oib.(ind_ctors) | None => []
              end in
            let anim_infos :=
              flat_map (fun '(rel_ind, (rel_nm, _)) =>
                let matching := filter (fun c => string_is_prefix rel_nm c.(cstr_name)) ctors in
                List.map (fun c =>
                  let orig_arg_types :=
                    List.rev (List.map (fun d =>
                      let t := unlift_arr d.(decl_type) in
                      match t with tRel _ => arr_t | _ => t end) c.(cstr_args)) in
                  let fnSymb_ty :=
                    List.fold_right (fun ty acc => tProd anon_b ty acc) (tInd fn_ind []) orig_arg_types in
                  (rel_ind, fn_ind, c.(cstr_name), fnSymb_ty))
                matching)
              kn_mode_list in
            tmReturn anim_infos)
            arr_name_pairs ;;
          arr_an_hole_infos <- tmEval all (List.concat arr_an_hole_infos_raw) ;;
          _ <- generate_animated_top_fn_prop
                  top_rel_nm type_minds type_mapping app_kn_mapping pi_set cur_mp
                  kn_mode_list unique_fn_infos true arr_an_hole_infos ;;
          tmMkDefinition (top_rel_nm ++ "TransparentSigma2AnimatedTopFn") composite
        | _, _ =>
          tmFail "animate_coinductive_with_fn_pos: cannot locate prod or animation_result (2)"
        end
      | None, _ => tmFail ("animate_coinductive_with_fn_pos: no mode entry for " ++ rfp_rel_nm)
      | _, None  => tmFail ("animate_coinductive_with_fn_pos: cannot find body " ++ rfp_rel_nm)
      end
    | _, _ => @tmFail unit "animate_coinductive_with_fn_pos: cannot locate prod or animation_result"
    end
  end.
Set Universe Checking.

Inductive test : (nat -> nat) -> nat -> nat -> Prop :=
| ctor0025 : forall f n, f n = (fun x y => x + y) (f 4) n -> test f n (n)
with test0 : ((nat -> nat) -> bool) -> (nat -> nat) -> bool -> Prop :=
| ctor3 : forall f g, f g = true /\ (fun y => y + 1) (g 4) = 5 /\ test (fun n => n + 1) 5 5  -> test0 f g true. 

MetaRocq Run (remove_from_fn_pos <? test ?> [("test", ([0;1], [2])); ("test0", ([0;1], [2]))]).

Print testremoveFnPos.
Print fnLam3.

Print test0removeFnPos.

(* Test: compute_lifted_arrow_types for the test/test0 example.
   Expected: arrow_types includes nat->nat (position 0 of test) and
   (nat->nat)->bool (position 0 of test0); type_kns unchanged since
   there are no a2i edges (no named function has an arrow output type
   in these constructors). *)
MetaRocq Run (
  let modes := [("test", ([0;1], [2])); ("test0", ([0;1], [2]))] in
  r <- compute_lifted_arrow_types modes [] 100 ;;
  let arrow_types := fst r in
  let type_kns    := snd r in
  tmMsg ("arrow_types count: " ++ string_of_nat #|arrow_types|) ;;
  tmMsg ("extended type_kns count: " ++ string_of_nat #|type_kns|)).

(* Test: lift_arrow_types_for_relation on a simple relation with one arrow-type
   input and a trivial constructor.
   Expected: declares [testFnLiftremoveFnPos] (same as testFnLift since no
   lambdas/var-apps in the constructor) and [fnType0] with one constructor
   [fnType0LiftCstr : (nat -> nat) -> fnType0].
   Wrapped in a Module to prevent fnType0/undefinedfnType0 from leaking into
   the global scope and conflicting with later animation runs. *)
Module TestLiftArrow.
Inductive testFnLift : (nat -> nat) -> nat -> Prop :=
| ctorFnLift0 : forall f, testFnLift f 0.

MetaRocq Run (lift_arrow_types_for_relation
  <? testFnLift ?>
  [("testFnLift", ([0], [1]))]
  []
  100).

Print testFnLiftremoveFnPos.
Print fnType0.
Print undefinedfnType0.
Print fnType0Lift.
Print fnType0PushPlain.
Print fnType0TransparentSigmaPushBody.
Print fnType0TransparentSigmaPush.
End TestLiftArrow.

