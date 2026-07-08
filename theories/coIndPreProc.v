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
(** ** Example: lift types for the Integrate relation                 *)
(* ================================================================== *)

(** Running this declares [nat'] and [stream'] in dependency order.
    [nat'] is declared first (no cross-type deps); [stream'] second.

    Expected result:
      CoInductive stream' : Type :=
        nil'         : stream'
      | Seq'         : nat' -> stream' -> stream'
      | IntegrateAn1 : stream' -> stream'            (* from Integrate output pos 1 *)
      | addStmAn2    : nat' -> stream' -> stream'.   (* from addStm output pos 2   *)

      Inductive nat' : Set :=
        O'          : nat'
      | S'          : nat' -> nat'
      | addNatAn2   : nat' -> nat' -> nat'.          (* from addNat output pos 2   *) *)
MetaRocq Run (
  mapping <- preprocess_coind_types
    [("Integrate", ([0], [1]));
     ("addStm",   ([0; 1], [2]));
     ("addNat",   ([0; 1], [2]))] ;;
  tmPrint mapping).
Print stream'.
Print nat'.  
  

(** Spot-check the declared types. *)
Check (nil'          : stream').
Check (Seq'          : nat' -> stream' -> stream').
Check (IntegrateAn1  : stream' -> stream').
Check (addStmAn2     : nat' -> stream' -> stream').
Check (O'            : nat').
Check (S'            : nat' -> nat').
Check (addNatAn2     : nat' -> nat' -> nat').
