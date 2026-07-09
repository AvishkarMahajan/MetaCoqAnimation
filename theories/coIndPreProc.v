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

(** Substitute every [tInd kn _] → [tInd kn' _] in a term according to
    [mapping : list (old_kn * new_kn)].  All other subterms are preserved. *)
Fixpoint subst_ind_kns (mapping : list (kername * kername)) (t : term) : term :=
  let lookup kn :=
    match find (fun p => eq_kername (fst p) kn) mapping with
    | Some (_, kn') => kn'
    | None          => kn
    end in
  match t with
  | tInd ind univs =>
    tInd {| inductive_mind := lookup (inductive_mind ind);
            inductive_ind  := inductive_ind ind |} univs
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
      {| ci_ind := {| inductive_mind := lookup (inductive_mind ci.(ci_ind));
                      inductive_ind  := inductive_ind ci.(ci_ind) |};
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

Definition subst_ind_kns_decl (mapping : list (kername * kername))
    (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map (subst_ind_kns mapping) d.(decl_body);
     decl_type := subst_ind_kns mapping d.(decl_type) |}.

(** Substitute a single term from a relation's [ind_indices] for use as a
    constructor argument type in a NEW constructor being added to a lifted type.

    Constructor types in MetaRocq Template use [tRel] for self-references
    (the type being declared), NOT [tInd new_kn].  Using [tInd] would cause
    a kernel anomaly because the type hasn't been added to the global
    environment yet when its own constructors are being checked.

    Convention: under [n_params] param binders, the [body_idx]-th type in a
    block of [n_bodies] is at de Bruijn index [n_params + n_bodies - 1 - body_idx].
    Under an additional [depth] arg binders the index shifts by [depth].

    - [self_old_kn] → [tRel (self_base + depth)]   (self-reference via relative index)
    - other old kns in [ext_mapping] → their new [tInd kn' _]   (already in env) *)
Definition subst_idx_type
    (self_old_kn : kername)
    (self_base   : nat)
    (ext_mapping : list (kername * kername))
    (depth       : nat)
    (t           : term) : term :=
  match t with
  | tInd ind univs =>
    let kn := inductive_mind ind in
    if eq_kername kn self_old_kn
    then tRel (self_base + depth)
    else match find (fun p => eq_kername (fst p) kn) ext_mapping with
         | Some (_, kn') =>
           tInd {| inductive_mind := kn'; inductive_ind := inductive_ind ind |} univs
         | None => t
         end
  | _ => t
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
    (old_kn         : kername)
    (body_idx       : nat)
    (n_bodies       : nat)
    (cparams        : context)
    (full_mapping   : list (kername * kername))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
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
        if existsb (eq_kername old_kn) (collect_tind_kns od.(decl_type))
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
                let t := subst_idx_type old_kn self_base ext depth d.(decl_type) in
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

(** Produce the lifted [mutual_inductive_body] for [old_kn] → [new_kn].
    [ext_mapping] maps all OTHER old types to their new counterparts.
    [modes_with_idx] provides the relation mode info and [ind_indices] contexts
    used to generate extra constructors (one per relation output position that
    targets this type). *)
Polymorphic Definition make_lifted_mind
    (old_mind       : mutual_inductive_body)
    (old_kn         : kername)
    (new_kn         : kername)
    (ext_mapping    : list (kername * kername))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    : mutual_inductive_body :=
  let full     := (old_kn, new_kn) :: ext_mapping in
  let params'  := List.map (subst_ind_kns_decl full) old_mind.(ind_params) in
  let n_bodies := #|old_mind.(ind_bodies)| in
  {| ind_finite    := old_mind.(ind_finite);
     ind_npars     := old_mind.(ind_npars);
     ind_universes := old_mind.(ind_universes);
     ind_variance  := old_mind.(ind_variance);
     ind_params    := params';
     ind_bodies    :=
       mapi (fun i oib =>
         let extra := compute_extra_cstrs old_kn i n_bodies params' full modes_with_idx in
         {| ind_name      := oib.(ind_name) ++ "'";
            ind_indices   := List.map (subst_ind_kns_decl full) oib.(ind_indices);
            ind_sort      := oib.(ind_sort);
            ind_type      := subst_ind_kns full oib.(ind_type);
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              List.map (fun c =>
                {| cstr_name    := c.(cstr_name) ++ "'";
                   cstr_args    := List.map (subst_ind_kns_decl full) c.(cstr_args);
                   cstr_indices := List.map (subst_ind_kns full) c.(cstr_indices);
                   cstr_type    := subst_ind_kns full c.(cstr_type);
                   cstr_arity   := c.(cstr_arity) |})
              oib.(ind_ctors) ++ extra;
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
    [fuel] bounds the number of passes (len + 1 is always sufficient for DAGs). *)
Fixpoint topo_sort_kns
    (remaining   : list kername)
    (minds_assoc : list (kername * mutual_inductive_body))
    (mapping     : list (kername * kername))
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
        match find (fun p => eq_kername (fst p) kn) minds_assoc with
        | Some (_, mind) => direct_deps_in_mapping kn mind mapping
        | None           => []
        end in
      let is_ready kn := forallb (fun dep => existsb (eq_kername dep) done) (deps_of kn) in
      let ready     := filter is_ready remaining in
      let not_ready := filter (fun kn => negb (is_ready kn)) remaining in
      match ready with
      | [] => List.app done remaining  (* cycle: append rest as-is *)
      | _  => topo_sort_kns not_ready minds_assoc mapping (List.app done ready) fuel
      end
    end
  end.

(** Given a [mode_map], find all non-Prop types occurring as argument types
    of the listed relations, declare a lifted copy [T'] for each one, and
    return the old → new kername mapping.

    For each relation output position that targets [T], the lifted type [T']
    gains an extra constructor:
      [RelNmAn{output_pos} : <lifted input types> -> T']

    Types with no matching output positions get only the renamed constructors
    (no extra constructors are added).  All types are declared in dependency
    order so that cross-type references are valid at declaration time. *)
Polymorphic Definition preprocess_coind_types
    (modes : mode_map)
    : TemplateMonad (list (kername * kername)) :=
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
  (* Step 4: collect types to lift — scan all input and output positions in
     ind_indices; exclude the relation types themselves *)
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
  (* Step 5: keep only non-Prop types *)
  type_kns <- monad_fold_left (fun acc kn =>
    mind <- tmQuoteInductive kn ;;
    if negb (is_prop_mind mind)
    then tmReturn (List.app acc [kn])
    else tmReturn acc)
    arg_kns [] ;;
  cur_mp <- tmCurrentModPath tt ;;
  let pre_mapping := List.map (fun kn => (kn, (cur_mp, snd kn ++ "'"))) type_kns in
  type_minds <- monad_map (fun kn =>
    mind <- tmQuoteInductive kn ;;
    tmReturn (kn, mind))
    type_kns ;;
  let sorted_kns :=
    topo_sort_kns type_kns type_minds pre_mapping [] (S #|type_kns|) in
  (* Step 6: declare types in topo order, resolving actual kns after each
     declaration so that cross-references use the kernel-registered names. *)
  actual_mapping <- monad_fold_left (fun acc kn =>
    match find (fun p => eq_kername (fst p) kn) type_minds with
    | None => tmFail "preprocess_coind_types: topo sort internal error"
    | Some (_, old_mind) =>
      let pre_new_kn := (cur_mp, snd kn ++ "'") in
      (* acc holds actual kns for types already declared; exclude self *)
      let ext := filter (fun q => negb (eq_kername (fst q) kn)) acc in
      tmMkInductivePreserveFinite (make_lifted_mind old_mind kn pre_new_kn ext modes_with_idx) ;;
      (* resolve the kn the kernel actually registered *)
      refs <- tmLocate (snd kn ++ "'") ;;
      let actual_kn :=
        match find (fun g => match g with IndRef _ => true | _ => false end) refs with
        | Some (IndRef actual_ind) => inductive_mind actual_ind
        | _                        => pre_new_kn
        end in
      tmReturn (List.app acc [(kn, actual_kn)])
    end)
    sorted_kns [] ;;
  tmReturn actual_mapping.


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

(** Substitute both [tInd] and [tConstruct] knames throughout a term.
    Constructor indices are preserved: the extra constructors appended to
    lifted types come after the originals, so original indices stay valid. *)
Fixpoint subst_inds_and_ctors (mapping : list (kername * kername)) (t : term) : term :=
  let lookup kn :=
    match find (fun p => eq_kername (fst p) kn) mapping with
    | Some (_, kn') => kn'
    | None          => kn
    end in
  match t with
  | tInd ind univs =>
    tInd {| inductive_mind := lookup (inductive_mind ind);
            inductive_ind  := inductive_ind ind |} univs
  | tConstruct ind idx univs =>
    tConstruct {| inductive_mind := lookup (inductive_mind ind);
                  inductive_ind  := inductive_ind ind |} idx univs
  | tEvar n args         => tEvar n (List.map (subst_inds_and_ctors mapping) args)
  | tCast c k v          => tCast (subst_inds_and_ctors mapping c) k
                                   (subst_inds_and_ctors mapping v)
  | tProd na ty body     => tProd na (subst_inds_and_ctors mapping ty)
                                      (subst_inds_and_ctors mapping body)
  | tLambda na ty body   => tLambda na (subst_inds_and_ctors mapping ty)
                                        (subst_inds_and_ctors mapping body)
  | tLetIn na val ty body =>
    tLetIn na (subst_inds_and_ctors mapping val)
              (subst_inds_and_ctors mapping ty)
              (subst_inds_and_ctors mapping body)
  | tApp f args =>
    tApp (subst_inds_and_ctors mapping f)
         (List.map (subst_inds_and_ctors mapping) args)
  | tCase ci pred disc brs =>
    let ci' :=
      {| ci_ind := {| inductive_mind := lookup (inductive_mind ci.(ci_ind));
                      inductive_ind  := inductive_ind ci.(ci_ind) |};
         ci_npar      := ci.(ci_npar);
         ci_relevance := ci.(ci_relevance) |} in
    let pred' :=
      {| pparams  := List.map (subst_inds_and_ctors mapping) pred.(pparams);
         puinst   := pred.(puinst);
         pcontext := pred.(pcontext);
         preturn  := subst_inds_and_ctors mapping pred.(preturn) |} in
    tCase ci' pred' (subst_inds_and_ctors mapping disc)
      (List.map (fun br =>
        {| bcontext := br.(bcontext);
           bbody    := subst_inds_and_ctors mapping br.(bbody) |}) brs)
  | tProj p c     => tProj p (subst_inds_and_ctors mapping c)
  | tFix mfix idx =>
    tFix (List.map (fun d =>
      {| dname := d.(dname);
         dtype := subst_inds_and_ctors mapping d.(dtype);
         dbody := subst_inds_and_ctors mapping d.(dbody);
         rarg  := d.(rarg) |}) mfix) idx
  | tCoFix mfix idx =>
    tCoFix (List.map (fun d =>
      {| dname := d.(dname);
         dtype := subst_inds_and_ctors mapping d.(dtype);
         dbody := subst_inds_and_ctors mapping d.(dbody);
         rarg  := d.(rarg) |}) mfix) idx
  | _ => t
  end.

Definition subst_inds_and_ctors_decl
    (mapping : list (kername * kername)) (d : context_decl) : context_decl :=
  {| decl_name := d.(decl_name);
     decl_body := option_map (subst_inds_and_ctors mapping) d.(decl_body);
     decl_type := subst_inds_and_ctors mapping d.(decl_type) |}.

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
    (type_mapping   : list (kername * kername))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    (type_body_map  : list (kername * one_inductive_body))
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
                decl_type := subst_ind_kns type_mapping d.(decl_type) |}])
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
              match collect_tind_kns d.(decl_type) with
              | [] => tVar "error_no_type"
              | old_kn :: _ =>
                let new_kn :=
                  match find (fun p => eq_kername (fst p) old_kn) type_mapping with
                  | Some (_, kn') => kn'
                  | None          => old_kn
                  end in
                let ctor_idx :=
                  match find (fun p => eq_kername (fst p) new_kn) type_body_map with
                  | Some (_, new_oib) =>
                    match find_ctor_idx extra_nm new_oib.(ind_ctors) 0 with
                    | Some i => i
                    | None   => 0
                    end
                  | None => 0
                  end in
                let new_ind := {| inductive_mind := new_kn; inductive_ind := 0 |} in
                if Nat.eqb n_inputs 0
                then tConstruct new_ind ctor_idx []
                else tApp (tConstruct new_ind ctor_idx []) input_var_list
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
    (type_mapping   : list (kername * kername))
    (modes_with_idx : list ((string * (list nat * list nat)) * list context_decl))
    (type_body_map  : list (kername * one_inductive_body))
    : mutual_inductive_body :=
  let full_mapping := (old_rel_kn, new_rel_kn) :: type_mapping in
  let params'  := List.map (subst_inds_and_ctors_decl full_mapping) old_mind.(ind_params) in
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
             type_mapping modes_with_idx type_body_map in
         {| ind_name      := oib.(ind_name) ++ "'";
            ind_indices   := List.map (subst_inds_and_ctors_decl full_mapping) oib.(ind_indices);
            ind_sort      := oib.(ind_sort);
            ind_type      := subst_inds_and_ctors full_mapping oib.(ind_type);
            ind_kelim     := oib.(ind_kelim);
            ind_ctors     :=
              List.map (fun c =>
                {| cstr_name    := c.(cstr_name) ++ "'";
                   cstr_args    := List.map (subst_inds_and_ctors_decl full_mapping) c.(cstr_args);
                   cstr_indices := List.map (subst_inds_and_ctors full_mapping) c.(cstr_indices);
                   cstr_type    := subst_inds_and_ctors full_mapping c.(cstr_type);
                   cstr_arity   := c.(cstr_arity) |})
              oib.(ind_ctors) ++ undef;
            ind_projs     := oib.(ind_projs);
            ind_relevance := oib.(ind_relevance) |})
       old_mind.(ind_bodies) |}.

(** Declare the lifted version of a mutual relation block.
    [modes] supplies the input/output positions for each body, used to
    build the Undefined constructors. *)
Polymorphic Definition lift_relation
    (rel_kn       : kername)
    (type_mapping : list (kername * kername))
    (modes        : mode_map)
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
    let new_kn := snd p in
    new_mind <- tmQuoteInductive new_kn ;;
    match new_mind.(ind_bodies) with
    | oib :: _ => tmReturn (new_kn, oib)
    | []       => @tmFail (kername * one_inductive_body) "lift_relation: empty lifted type"
    end)
    type_mapping ;;
  tmMkInductivePreserveFinite
    (make_lifted_relation_mind old_mind rel_kn new_rel_kn type_mapping modes_with_idx type_body_map).


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
  kns <- monad_fold_left (fun acc nm =>
    refs <- tmLocate nm ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [inductive_mind ind])
    | _ => tmFail ("lift_relation_names: cannot find '" ++ nm ++ "'")
    end)
    all_nms [] ;;
  match kns return TemplateMonad unit with
  | rel_kn :: kns_rest =>
    lift_relation rel_kn (pair_up kns_rest) modes
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
  rel_kn_list <- monad_fold_left (fun acc nm =>
    refs <- tmLocate nm ;;
    match find (fun g => match g with IndRef _ => true | _ => false end) refs with
    | Some (IndRef ind) => tmReturn (List.app acc [inductive_mind ind])
    | _ => tmFail ("lift_coinductive_relation: cannot find '" ++ nm ++ "'")
    end)
    [rel_nm] [] ;;
  match rel_kn_list return TemplateMonad unit with
  | [rel_kn] =>
    type_mapping <- preprocess_coind_types modes ;;
    lift_relation rel_kn type_mapping modes
  | _ => @tmFail unit "lift_coinductive_relation: failed to resolve relation"
  end.


(* ================================================================== *)
(** ** Example: lift Integrate and its coinductive types               *)
(* ================================================================== *)

MetaRocq Run (lift_coinductive_relation "Integrate"
               [("Integrate", ([0],    [1]));
                ("addStm",   ([0; 1], [2]));
                ("addNat",   ([0; 1], [2]))]).

(** Lifted data types. *)
Print stream'. Print nat'.
Check (nil'         : stream').
Check (Seq'         : nat' -> stream' -> stream').
Check (IntegrateAn1 : stream' -> stream').
Check (addStmAn2    : nat' -> stream' -> stream').
Check (O'           : nat').
Check (S'           : nat' -> nat').
Check (addNatAn2    : nat' -> nat' -> nat').

(** Lifted relations. *)
Print Integrate'. Print addStm'. Print addNat'.
Check (integNil'           : Integrate' nil' nil').
Check (integ'              : forall s2 s3 n s5,
         Integrate' s2 s3 /\ addStm' n s3 s5 ->
         Integrate' (Seq' n s2) (Seq' n s5)).
Check (Integrate'Undefined : forall v0, Integrate' v0 (IntegrateAn1 v0)).
Check (addStmNil'          : forall m, addStm' m nil' nil').
Check (plusm'              : forall m s1 n n' s2,
         addStm' m s1 s2 /\ addNat' m n n' ->
         addStm' m (Seq' n s1) (Seq' n' s2)).
Check (addStm'Undefined    : forall v0 v1, addStm' v0 v1 (addStmAn2 v0 v1)).
Check (addZero'            : forall n, addNat' O' n n).
Check (addSucc'            : forall n m p, addNat' n m p -> addNat' (S' n) m (S' p)).
Check (addNat'Undefined    : forall v0 v1, addNat' v0 v1 (addNatAn2 v0 v1)).
