(** * AnimationSoundnessTactics: generalized tactics for proving soundness
    of [animate_inductive]-generated [<Rel>AnimatedTopFn] functions.

    Scratch/working file. Built by generalizing the three hand-proofs in
    TestSoundnessAdd.v / TestSoundnessStack.v / TestSoundnessSTLC.v. Those
    files are NOT modified; this file provides a reusable tactic library
    that is validated by re-deriving (a copy of) each of those soundness
    theorems with minimal per-relation glue below. *)

Require Import Animation.AnimationResult.
Require Import Animation.TermUtils.
Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.
Require Import Animation.EqualityResolution.
Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.
Import MetaRocqNotations.
Local Open Scope nat_scope.
Open Scope bs.

(** Most [eqFn]s seen so far (e.g. [eqFnty], [eqFnsinstr]) are generated
    the SAME mechanical way: [Definition eqFn (a b : T) : bool := if
    decEq a b then true else false] wrapping a [decide equality]-derived
    decision procedure. That means its soundness fact has exactly one
    fixed shape every time, decidable straight from whatever hypothesis
    [H : eqFn a b = true] is already sitting in context: unfold whatever
    [eqFn] turns out to be (read off [H], not hardcoded), destruct the
    underlying decision procedure, and the [true]/[false] branches are
    [exact]/[discriminate] respectively. So for THAT shape there's no
    need to ever state or prove a standing [Lemma eqFn_sound : forall a
    b, eqFn a b = true -> a = b] -- [eqfn_sound_inline H] discharges the
    fact INLINE, on the spot, wherever a guard's hypothesis is already
    in hand (see [resolve_eqfn_guards] below). *)
Ltac eqfn_sound_inline H :=
  match type of H with
  | ?eqFn ?a ?b = true =>
      unfold eqFn in H;
      match type of H with
      | (if ?dec a b then true else false) = true =>
          destruct (dec a b) as [Heq | Hneq]; [ exact Heq | discriminate H ]
      end
  end.

(** A hand-written, non-[decide-equality] [eqFn] (e.g. one built from
    [andb]/[Nat.leb] rather than [if decEq a b then true else false])
    is the one case [eqfn_sound_inline] genuinely can't handle -- its
    inner [match] simply has no clause for whatever shape the body
    unfolds to, and that failure is NOT silently swallowed: it surfaces
    as a hard, visible proof failure at the enclosing [Qed] (confirmed:
    "No matching clauses for match"), not a silently-wrong or
    vacuously-passing proof. For exactly that case, [eqfn_sound] is an
    OPT-IN escape hatch, not the default path: prove your own ordinary
    [Lemma my_eqFn_sound : forall a b, my_eqFn a b = true -> a = b] by
    whatever means the hand-written definition actually needs, register
    it with [Hint Resolve my_eqFn_sound : eqfn_sound], and
    [resolve_eqfn_guards]/[try_constructors] below automatically fall
    back to it whenever [eqfn_sound_inline] doesn't apply. Every
    [decide-equality]-shaped [eqFn] still needs nothing registered here
    at all -- this database stays empty unless a hand-written case
    actually comes up. *)
Create HintDb eqfn_sound.

(** One case is NOT a per-relation hand-written [eqFn] at all, but comes
    up constantly: whenever a clause's pattern uses the SAME bound
    variable in two argument positions (e.g. [suffixCons]'s [w] heading
    both the input list and the adjacent output-side list), the engine
    has to compile that into a RUNTIME equality check between whatever
    the two positions actually hold at animation time -- for [nat], that
    check is literally [Nat.eqb]/[=?], which (being an ordinary
    structurally-recursive [Fixpoint], not a [decide-equality] wrapper)
    [eqfn_sound_inline] can't unfold either. Since this is fundamental
    and ubiquitous (not something a user writes per custom type), its
    soundness fact is registered HERE, once, permanently, rather than
    re-derived in every validation that happens to pattern-match on
    repeated [nat] variables. *)
Lemma Nat_eqb_sound : forall n m : nat, (n =? m) = true -> n = m.
Proof. apply PeanoNat.Nat.eqb_eq. Qed.

Hint Resolve Nat_eqb_sound : eqfn_sound.

(** Same story one level up: when the REPEATED variable's type is a
    [list], e.g. two independently-animated calls that both have to
    agree on some shared list-valued argument (because they were fed to
    SEPARATE, empty-input-mode relations with no way to pass that list
    in as a common input), the engine checks equality via MetaRocq's
    own [eqb_list] (parametrized by the element type's own [eqb]) --
    structurally recursive, not [decide-equality]-shaped, same gap as
    [Nat.eqb]. This lemma is deliberately generic (any element type [A]
    with its OWN soundness fact as a hypothesis) rather than hardcoded
    to [nat], so [eauto with eqfn_sound] can chain it with
    [Nat_eqb_sound] (or any other registered element-soundness lemma)
    automatically to cover [list nat], [list (list nat)], etc. without
    a separate registration per element type. *)
Lemma eqb_list_sound : forall (A : Type) (eqA : A -> A -> bool),
  (forall a b : A, eqA a b = true -> a = b) ->
  forall l1 l2 : list A, eqb_list eqA l1 l2 = true -> l1 = l2.
Proof.
  intros A eqA Hsound.
  induction l1 as [|a l1 IH]; intros [|b l2] H; simpl in H; try discriminate H.
  - reflexivity.
  - destruct (eqA a b) eqn:Hab; try discriminate H.
    f_equal; [apply Hsound; assumption | apply IH; assumption].
Qed.

Hint Resolve eqb_list_sound : eqfn_sound.

(* ==================================================================== *)
(** ** Part 1: generic, relation-independent facts about [dispatch_ind_ext].
    Proven once; every generated [<Rel>AnimatedTopFn] re-embeds its own
    fresh kernel copy, so these are used via the [bridge_dispatch_ind_ext]
    tactic below rather than by [rewrite]-ing a fixed name. *)
(* ==================================================================== *)

Lemma dispatch_ind_ext_success_inv :
  forall (A B : Type) (lst : list (nat -> animation_result A -> animation_result B))
         (F : nat) (input : animation_result A) (out : B),
  dispatch_ind_ext A B lst F input = Success B out ->
  exists h m, In h lst /\ m < F /\ h m input = Success B out.
Proof.
  intros A B lst.
  induction lst as [|h t IH]; intros F input out Hdis.
  - cbn [dispatch_ind_ext] in Hdis. destruct F; discriminate Hdis.
  - destruct F as [|k].
    + cbn [dispatch_ind_ext] in Hdis. discriminate Hdis.
    + cbn [dispatch_ind_ext] in Hdis.
      destruct (h k input) as [|w|] eqn:Hh.
      * discriminate Hdis.
      * injection Hdis as <-.
        exists h, k. split; [left; reflexivity|]. split; [lia|]. exact Hh.
      * destruct (IH k input out Hdis) as [h' [m' [Hin [Hlt Heq]]]].
        exists h', m'. split; [right; exact Hin|]. split; [lia|]. exact Heq.
Qed.

Lemma dispatch_ind_ext_ext :
  forall (A B : Type)
    (D : list (nat -> animation_result A -> animation_result B) ->
         nat -> animation_result A -> animation_result B),
  (forall lst input, D lst 0 input = FuelError B) ->
  (forall lst n input, D lst (S n) input =
     match lst with
     | [] => NoMatch B
     | h :: t =>
         match h n input with
         | NoMatch => D t n input
         | FuelError => FuelError B
         | Success w => Success B w
         end
     end) ->
  forall n lst input, D lst n input = dispatch_ind_ext A B lst n input.
Proof.
  intros A B D HD0 HDS n.
  induction n as [|n IH]; intros lst input.
  - rewrite HD0. cbn [dispatch_ind_ext]. reflexivity.
  - rewrite HDS. cbn [dispatch_ind_ext].
    destruct lst as [|h t]; [reflexivity|].
    destruct (h n input) as [|w|] eqn:Hh; try reflexivity.
    apply IH.
Qed.

(** Proves "[D] satisfies [dispatch_ind_ext]'s own two defining equations"
    for WHATEVER concrete [D] the caller's goal already names (typically
    produced by a preceding [cbn] that exposed an embedded copy) -- the
    second obligation here is always the same two-line unfold+destruct,
    regardless of which relation's embedded dispatcher [D] happens to be.

    Uses [fresh]-generated names throughout, NOT hardcoded ones: this
    tactic can run inside an [assert] whose goal already has its own
    binders in scope from the caller (e.g. [STLCValidation]'s [TVar]
    case calls it from inside a context that already has an [n0] bound,
    from [e = tvar n0]) -- hardcoded names here ("n0" was the original
    culprit) can collide with those and fail with "n0 is already used",
    even though the two [n0]s have nothing to do with each other. *)
Ltac bridge_dispatch_ind_ext :=
  let lst0 := fresh "lst0" in
  let n0 := fresh "n0" in
  let input0 := fresh "input0" in
  let h0 := fresh "h0" in
  let t0 := fresh "t0" in
  let w := fresh "w" in
  apply dispatch_ind_ext_ext;
  [ reflexivity
  | intros lst0 n0 input0;
    destruct lst0 as [|h0 t0]; [reflexivity|];
    destruct (h0 n0 input0) as [|w|]; reflexivity ].

(* ==================================================================== *)
(** ** Part 2: unfolding one [<Rel>AnimatedTopFn] dispatch step.

    [unfold_dispatch_step H] turns a hypothesis
      [H : TopFn (S rem_fuel) input = Success _ out]
    into
      [h], [m], [Hlt : m < rem_fuel], [H : h m input = Success _ out],
      [Hin : In h [Clause1; Clause2Animated TopFn; ...]]
    one goal per list element -- [TopFn] is a named global, delta-unfolded
    by plain [cbn], converging on [finish_dispatch_unfold] once [H]'s
    head is exposed as a [dispatch_ind_ext]-shaped application. *)
(* ==================================================================== *)

Ltac finish_dispatch_unfold H :=
  match type of H with
  | ?D ?A ?B ?lst ?fl ?inp = _ =>
      let Hbridge := fresh "Hbridge" in
      assert (Hbridge : D A B lst fl inp = dispatch_ind_ext A B lst fl inp)
        by bridge_dispatch_ind_ext;
      rewrite Hbridge in H; clear Hbridge
  end;
  apply dispatch_ind_ext_success_inv in H;
  let h := fresh "h" in
  let m := fresh "m" in
  let Hin := fresh "Hin" in
  let Hlt := fresh "Hlt" in
  destruct H as [h [m [Hin [Hlt H]]]];
  simpl in Hin;
  repeat (destruct Hin as [<- | Hin]);
  try (exfalso; exact Hin).

Ltac unfold_dispatch_step H := cbn in H; finish_dispatch_unfold H.

(* ==================================================================== *)
(** ** Part 3: saturating one clause's hypothesis.

    After [unfold_dispatch_step], each resulting goal has
      [H : ClauseXAnimated ... m input = Success _ out]
    (and the clause may take further animated-function arguments for its
    own recursive premises). [saturate_clause ClauseFn H] unfolds
    [ClauseFn] and the combinator plumbing, then repeatedly resolves every
    "stuck" subterm it can find in [H] -- a bare pattern variable driving
    the clause's own [match], a not-yet-evaluated recursive/sibling call
    (type [animation_result _]), or a not-yet-evaluated boolean [eqFn]
    guard -- calling [simpl] after each step, until nothing further
    reduces. Crucially this NEVER calls [discriminate] mid-saturation:
    [and_outcome_bool]/[eq_outcome]'s compiled [match]es can stay stuck on
    one leg even when the overall branch is "obviously" impossible, so
    every potentially-stuck subterm must be resolved before any branch is
    judged to be a contradiction (this was the main lesson from the [TAdd]/
    [TApp] cases in TestSoundnessSTLC.v). *)
(* ==================================================================== *)

(** [cbn beta iota zeta in H] (no delta at all), NOT [simpl in H]: once a step below destructs the fuel
    variable (or any other bare variable) into [S n], every self- or
    sibling-recursive call still mentioned in [H] -- e.g.
    [addAnimatedTopFn (S n) input] -- suddenly becomes a valid iota-redex
    too, and an UNRESTRICTED [simpl]/[cbn] greedily unfolds the ENTIRE
    recursive definition right there (exposing its raw [fix]/
    [dispatch_ind_ext] body) instead of leaving it as the opaque,
    case-splittable application the second [saturate_step] branch below
    is looking for. An explicit (here empty) bracket list restricts
    [cbn]'s delta (unfolding of NAMED constants) to nothing, while still
    performing the beta/iota/zeta reduction needed to collapse a [match]
    once its scrutinee is concrete -- exactly the two things wanted. *)
(** NOT restricted to [type of H]: destructuring one stuck subterm can
    spawn a BRAND NEW, separate hypothesis (via [destruct ... eqn:Heq])
    that itself still has a further stuck subterm inside IT -- confirmed
    twice now (a [reduceToBool]-wrapped sibling call left stuck inside a
    freshly-made [Heq], and a ground-pattern [match] on [wrap_nat n]
    left stuck inside a freshly-made [Heqo]) -- and a version of this
    tactic tied to one fixed [H] can never see those, since they are NOT
    part of [H]'s own type anymore once spawned. Scanning the whole
    goal's hypotheses (via [match goal with _ : context[...] |- _ =>])
    instead of just [type of H] means a newly-spawned hypothesis is
    exactly as reachable on the NEXT [repeat] iteration as the original
    [H] was, with no special-casing needed. *)
Ltac saturate_step :=
  first
    [ match goal with
      | _ : context [ match ?x with _ => _ end ] |- _ => is_var x; destruct x eqn:?
      end
    | match goal with
      | _ : context [ match ?call with _ => _ end ] |- _ =>
          lazymatch type of call with
          | animation_result _ =>
              (* Exclude candidates that are themselves a bare [match]: those
                 are an outer, not-yet-reduced combinator result (which also
                 happens to type-check as [animation_result _]), not the true
                 innermost recursive/sibling-call application. Failing here
                 makes Ltac's [context] search backtrack to a different
                 occurrence instead of destructuring the wrong (premature)
                 subterm. *)
              lazymatch call with
              | match _ with _ => _ end => fail
              | _ => destruct call eqn:?
              end
          end
      end
    | match goal with
      | _ : context [ if ?cond then _ else _ ] |- _ => destruct cond eqn:?
      end
    | (* A ground-pattern/function-application equality guard (e.g.
         [nulCon = wrap_nat n]) compiles to a bare [match] on a
         user-defined function's result -- NOT a bare variable (so the
         first alternative above doesn't apply), NOT [animation_result]-
         typed (so the second alternative doesn't apply either, it's
         some other custom inductive like [newTp]), and not an [if].
         Same "exclude an outer not-yet-reduced bare [match]" guard as
         the stuck-call case, for the same reason: don't grab a
         premature outer combinator result instead of the true
         innermost stuck scrutinee. *)
      match goal with
      | _ : context [ match ?scrut with _ => _ end ] |- _ =>
          lazymatch type of scrut with
          | animation_result _ => fail
          | _ =>
              lazymatch scrut with
              | match _ with _ => _ end => fail
              | _ => destruct scrut eqn:?
              end
          end
      end
    ]; cbn beta iota zeta in *.

(** [cbn]/[simpl] without an explicit name list are conservative: they
    won't delta-unfold a clause function whose body would still be stuck
    on free-variable scrutinees afterward (the hand-proofs always named
    the clause function explicitly, e.g. [unfold add_zeroAnimated]). The
    generic tactic can't hard-code that name, but [H]'s own head symbol
    IS that name, so [match type of H with ?F _ _ = _ => unfold F in H
    end] reads it off and unfolds it by reference -- tried at a few
    arities since a clause may take leading higher-order arguments
    before fuel/input: ONE for a self-recursive clause (e.g.
    [add_succAnimated f m input]), but potentially MORE when a single
    clause's premise calls several DIFFERENT sibling relations (e.g.
    [isG2Animated]'s clause needs both [isGoodEmptyInAnimatedTopFn] and
    [isGoodEmptyIn'AnimatedTopFn] passed in, for arity 4 overall) --
    confirmed empirically that arity 1-3, tried SMALLEST FIRST, is not
    enough and not even safe in general: a too-small arity still lets
    [?F] bind to a genuinely partially-applied (not bare) term -- e.g.
    for [isG2Animated sib1 sib2 fuel input] (arity 4: two leading
    sibling-relation calls, then fuel/input), the arity-1 pattern binds
    [?F] to [isG2Animated sib1 sib2 fuel], and [unfold F in H] on THAT
    doesn't error, it just does something useless, so [first] stops
    there and never reaches the arity that actually matches the bare
    head. Trying LARGEST arity first instead fixes this soundly: a
    too-LARGE arity has no way to unify at all (there aren't that many
    real arguments to peel off), so it fails cleanly and [first] moves
    down, meaning the exact matching arity -- the only one where [?F]
    is forced to be the bare, genuinely-unfoldable head -- is always
    reached before any smaller, partially-applied false match gets a
    chance. Tried up to 6 (comfortably more leading sibling calls than
    any relation needs in one clause); extend further if a future
    relation's clause ever calls more siblings than that in one go. *)
Ltac unfold_clause_head H :=
  first
    [ match type of H with ?F _ _ _ _ _ _ = _ => unfold F in H end
    | match type of H with ?F _ _ _ _ _ = _ => unfold F in H end
    | match type of H with ?F _ _ _ _ = _ => unfold F in H end
    | match type of H with ?F _ _ _ = _ => unfold F in H end
    | match type of H with ?F _ _ = _ => unfold F in H end
    | match type of H with ?F _ = _ => unfold F in H end
    | idtac ].

(** These library-level combinator names ARE fixed (not per-relation), so
    unlike the clause function's own name, the generic tactic can just
    hard-code them -- same list as the hand-proofs' [unfold_combinators]. *)
Ltac unfold_combinators_in H :=
  unfold compose_outcome, compose_outcome_no_in, option_to_result, join_pair, join_unit,
         split_outcome_fst, split_outcome_snd,
         with_default, dispatch_clauses, fuel_error_fn,
         and_outcome_bool, eq_outcome, id_fn, reduceToBool, Bool.eqb in H.

Ltac saturate_clause H :=
  unfold_clause_head H; unfold_combinators_in H; cbn beta iota zeta in H;
  repeat saturate_step.

(* ==================================================================== *)
(** ** Part 4: shared primitives for closing a saturated clause once its
    recursive-call hypotheses have been resolved into facts about the
    source relation(s) -- picking the matching constructor, discharging
    [eqFn] guards first. The "resolve recursive calls via the induction
    hypothesis" loop itself lives next to whichever entry point needs it
    (see [close_clause_joint] in Part 5): it only ever touches hypotheses
    of the exact shape [H : <SomeTopFn> <fuel> <input> = Success _ <v>]
    via [repeat], which terminates gracefully (not in an infinite loop,
    not with a propagated error) as soon as no remaining such hypothesis
    unifies against the induction hypothesis. *)
(* ==================================================================== *)

(** Plain [econstructor] commits to the first constructor whose
    CONCLUSION unifies and never reconsiders if the resulting side-goals
    turn out unprovable -- fine when constructors have distinguishing
    conclusions (like [add]'s), but WRONG when every constructor shares
    one generic conclusion and the distinguishing structure lives
    entirely in the premises (like [stack_step]'s five constructors,
    which all conclude [stack_step st ps0 ps1]): it would always commit
    to the first one and then get stuck on an unprovable premise. Trying
    each numbered constructor explicitly under [first] gives real
    backtracking -- each alternative restarts from the original goal, so
    a follow-up [eauto] failure correctly moves on to the next
    constructor instead of getting stuck. 8 is comfortably more
    constructors than any relation seen so far; [econstructor N] fails
    cleanly (letting [first] move on) once a relation has fewer. *)
(** [solve [...]], not bare [eauto ...]: when a constructor's leftover
    premise is an UNPROVABLE equality between two different constructors
    (e.g. trying [SS_Push] against an [SLoad]-headed input), [eauto] can
    still report "success" by SHELVING the still-open, metavariable-laden
    goal instead of actually closing it or failing -- which would make
    [first] think this (wrong) constructor worked and never try the next
    one. [solve] requires the goal, shelved subgoals included, to end up
    FULLY closed, so a bad constructor choice now genuinely fails and
    [first] backtracks to the next one. *)
Ltac try_constructors :=
  first
    [ econstructor 1; solve [ eauto with eqfn_sound ]
    | econstructor 2; solve [ eauto with eqfn_sound ]
    | econstructor 3; solve [ eauto with eqfn_sound ]
    | econstructor 4; solve [ eauto with eqfn_sound ]
    | econstructor 5; solve [ eauto with eqfn_sound ]
    | econstructor 6; solve [ eauto with eqfn_sound ]
    | econstructor 7; solve [ eauto with eqfn_sound ]
    | econstructor 8; solve [ eauto with eqfn_sound ] ].

(** The common tail shared by every [close_clause*] variant: once every
    recursive premise has been turned into a fact about the SOURCE
    relation, this is just "discriminate the impossible branch, or
    inject+pick a constructor". *)
(** For each still-boolean [eqFn] guard fact in context (e.g. [Heqb :
    eqFnty TBool t = true]), the derived propositional equality ([TBool
    = t]) alone won't get rewritten back into some other, already-
    established recursive-call fact (e.g. turning [typing cxt t2 t]
    into [typing cxt t2 TBool]) -- so this has to be an explicit step,
    before constructor selection: turn every [eqFn a b = true] into
    [a = b] and [subst] it in, just like the hand-proof's explicit
    [apply eqFnty_sound in ...] calls used to. [eqfn_sound_inline H] is
    tried FIRST (no lemma needed, covers the common [decide-equality]
    case), falling back to [eauto with eqfn_sound] -- empty by default,
    populated only if a hand-written [eqFn] needed its own registered
    lemma (see the comment above [Create HintDb eqfn_sound] for why
    that's rare and opt-in, not the default path). *)
Ltac resolve_eqfn_guards :=
  repeat match goal with
  | H : ?eqFn ?a ?b = true |- _ =>
      let Heq := fresh "Heq" in
      assert (Heq : a = b) by (first [ eqfn_sound_inline H | eauto with eqfn_sound ]);
      clear H; subst
  end.

(** [saturate_clause] only ever tracks and simplifies ONE hypothesis
    ([H]/[Hanim]) -- but [saturate_step]'s [if cond then _ else _]
    branch, when [cond] itself contains a nested not-yet-resolved call
    (e.g. a ground-equality guard compiled as [Bool.eqb true
    (reduceToBool (SiblingAnimatedTopFn ...))]), commits to a case split
    on [cond] via [destruct cond eqn:Heq] BEFORE that nested call has a
    chance to be resolved to something concrete -- leaving [Heq] (a
    SEPARATE hypothesis, not part of [H]'s own type) holding whatever
    [cond] turned out to actually equal once the sibling call's outcome
    becomes known (confirmed: e.g. [Heq : true = Bool.eqb true false]
    once [reduceToBool]/[Bool.eqb] are unfolded and the sibling call's
    own outcome is substituted in). [saturate_clause]/[close_clause_joint]
    never look at [Heq], only [H], so a branch that's ACTUALLY impossible
    this way is never discriminated away. This sweeps every equality
    hypothesis in context (not just [H]) and discharges whichever ones
    are already-contradictory [discriminate]-style facts; [discriminate]
    failing on a genuinely consistent equality is a normal, recoverable
    failure, so [match goal]'s backtracking just moves on. *)
Ltac discriminate_stray_contras :=
  repeat match goal with
  | H' : _ = _ |- _ => discriminate H'
  end.

Ltac finish_success H :=
  resolve_eqfn_guards;
  discriminate_stray_contras;
  first
    [ discriminate H
    | injection H as ?; subst; try_constructors
    | try_constructors ].

(* ==================================================================== *)
(** ** Part 5: one-shot entry points for the common case -- EVERY
    relation animated together in ONE [modes] bundle passed to a single
    [animate_inductive] call, where every clause across the whole bundle
    is self-recursive, calls ANOTHER relation in the SAME bundle (named
    or not, dependency cycle or not), or uses an [eqFn] guard already
    registered in [eqfn_sound]. This is the actual "push a button"
    tactic: state ONE joint [Lemma bundle_soundness_aux : forall n,
    SoundA n /\ SoundB n /\ ...] (one conjunct per relation, in any
    order) and prove its WHOLE body with [animation_soundness_proof_joint]
    -- no per-clause code, no per-relation [Fixpoint]/depth bookkeeping,
    no need to even ask whether the bundle's relations depend on each
    other. Each relation's own user-facing [Theorem] is then a one-liner
    via [animation_soundness_project bundle_soundness_aux]. See the big
    comment just above [animation_soundness_proof_joint]'s definition
    for the full design rationale (including the genuinely-cyclic case).

    The ONE case this doesn't cover: a relation animated by a truly
    SEPARATE [animate_inductive] call that some OTHER bundle's clause
    calls into -- each separate call re-derives its own unrelated,
    un-nameable mutual block from scratch, so the callee's embedded copy
    inside the caller's dispatch has no name [animation_soundness_proof_joint]
    (or anything else in this file) can refer to. Nothing here currently
    handles that case; see git history for the [close_sibling_clause]
    extraction technique this file used to carry for exactly that
    situation, if it comes up again. *)
(* ==================================================================== *)

Ltac simpl_discriminate H := simpl in H; discriminate H.

(** [animation_soundness_proof_joint]/[animation_soundness_project]: the
    push-button form for proving soundness for every relation in ONE [modes]
    bundle together. Rather than one artificial depth-bounded [Fixpoint]
    PER relation (needing a separate wrapper [Theorem] to strip the
    bound, and -- for bundled siblings -- some way to hand multiple IHs
    around), build exactly ONE auxiliary [Lemma]:
      [forall n, SoundA n /\ SoundB n /\ SoundC n /\ ...]
    (one conjunct per relation in the bundle, right-nested), proved ONCE
    by well-founded (strong) induction on [n] via [lt_wf_ind] -- which
    needs no artificial bound at all, so there's nothing to strip
    afterward -- then each relation's user-facing [Theorem] is just a
    one-line projection out of it.

    This is uniform regardless of whether the bundle's relations depend
    on each other: [repeat split] after [induction n using lt_wf_ind]
    decomposes the conjunction into one goal per relation (0 splits,
    i.e. a no-op, when there's only one relation -- self-recursion-only
    or no-recursion-at-all both fall out of the SAME call with zero
    special-casing), and each resulting goal's own recursive-call
    hypotheses get closed by projecting WHICHEVER conjunct of [IH]
    happens to head-match, exactly the same "try it, let a wrong guess
    fail cleanly" discipline used everywhere else in this file. This
    also happens to be the right tool for a genuinely CYCLIC pair of
    relations (A needs B's soundness at smaller fuel and vice versa) --
    a case that CANNOT be handled by proving one relation's soundness to
    completion before the other even starts, since well-founded
    induction on the shared fuel gives ONE joint IH covering every
    relation at every smaller fuel value in a single step, with no need
    to manually chase a "soundness of A at n depends on B at n-1 depends
    on A at n-2..." chain by hand.

    When the bundle has only ONE relation (e.g. [add], [stack_step]
    below), there is no [_aux]/wrapper split at all: with no artificial
    bound to strip, the joint statement and the one relation's final
    user-facing statement are THE SAME TYPE, so
    [animation_soundness_proof_joint] goes directly on the [Theorem].
    [animation_soundness_project] (and a separately-named [_aux]
    [Lemma]) is only needed when TWO OR MORE user-facing [Theorem]s in
    the same bundle must share one proof -- e.g. [typing_soundness] and
    [lookup_soundness] below both projecting out of
    [typing_lookup_soundness_aux] -- since Coq has no way to reuse a
    proof across multiple top-level statements other than giving the
    shared proof its own name once. (Plain Ltac also has no way to
    introduce that shared name as a side effect of proving one of the
    two [Theorem]s -- a tactic only ever transforms the goal it's
    already inside, it can't emit a new top-level declaration -- so for
    a genuinely multi-relation bundle, the one extra [Lemma] line here
    is the minimum needed to avoid re-deriving the whole induction once
    per sibling [Theorem].) *)

(** [try_ih_conjuncts H ih] tries, in order: (1) [ih] itself is already
    the exact fact needed (the bundle has only one relation, so [IH] is
    a bare statement, not a conjunction at all); (2) [ih]'s FIRST
    conjunct is the one needed; (3) recurse into [ih]'s remaining
    conjuncts. Each alternative instantiates [ih]'s own leading [forall
    m, m < n -> ...] with metavariables and lets [eapply ... in H]
    unify them against whatever fuel/shape [H] already has -- [m] is
    never chosen up front, it's always discovered by unification. A guess that's
    the wrong shape (e.g. trying [proj1] on a fact that isn't actually a
    conjunction, or on the wrong relation) is a normal, recoverable
    elaboration/unification failure, so [first] just falls through. *)
Ltac try_ih_conjuncts H ih :=
  first
    [ eapply (fun m Hlt => ih m Hlt) in H; [ | lia ]
    | eapply (fun m Hlt => proj1 (ih m Hlt)) in H; [ | lia ]
    | try_ih_conjuncts H (fun m Hlt => proj2 (ih m Hlt)) ].

Ltac close_clause_joint H IH :=
  repeat match goal with
  | H' : _ = Success _ _ |- _ => try_ih_conjuncts H' IH
  end;
  finish_success H.

Ltac animation_soundness_step_joint unfoldtac zerotac IH :=
  intros;
  match goal with
  | Hanim : ?F ?n0 _ = Success _ _ |- _ =>
      destruct n0 as [|rem_fuel];
      [ zerotac Hanim
      | unfoldtac Hanim; saturate_clause Hanim; close_clause_joint Hanim IH ]
  end.

(** Guarded [split], NOT bare [repeat split]: plain [split] is not
    safely restricted to the joint statement's own top-level [/\]
    chain. Coq's [split] is really "intro whatever's needed, then apply
    the sole constructor of a single-constructor inductive" -- so on a
    goal like [forall l m, TopFn ... -> SomeRel l m] where [SomeRel]
    itself happens to have EXACTLY ONE constructor
    (e.g. a relation like [isGood2] whose one constructor's premise is
    itself a [/\]), bare [split] will silently intro through the
    [forall]/arrow AND apply [SomeRel]'s own constructor, confirmed via
    a minimal reproduction -- completely bypassing the fuel-dispatch
    reasoning [animation_soundness_step_joint] is supposed to run on
    that goal. Every relation in this file with 2+ constructors masked
    this (bare [split] can't touch a goal headed by an un-introduced
    [forall], so with 2+ constructors there's no single-constructor
    goal for it to eagerly unfold) -- a single-constructor relation
    bundled with others (like [isGood2]/[isGoodEmptyIn]/[isGoodEmptyIn'])
    exposes it immediately. The fix: GUARD [split] so it only ever fires
    when the CURRENT goal is ALREADY, syntactically, [_ /\ _] at the top
    -- that's always true for the joint conjunction's own structure
    (right after [induction ... using lt_wf_ind], there is no leading
    [forall] left to hide behind), and never true for an individual
    relation's still-forall-headed goal, so this can never reach into
    unfolding some OTHER relation's constructor by accident. *)
Ltac animation_soundness_proof_joint :=
  let n := fresh "n" in
  let IH := fresh "IH" in
  intros n; induction n as [n IH] using lt_wf_ind;
  repeat match goal with |- _ /\ _ => split end;
  animation_soundness_step_joint unfold_dispatch_step simpl_discriminate IH.

(** [animation_soundness_project joint_lemma] is the user-facing
    [Theorem]'s whole proof: instantiate the joint [Lemma] at this
    [Theorem]'s own fuel value (read off [Hanim], not a hardcoded name,
    same discipline as [animation_soundness_step_joint] above),
    then [finish_from_conjunct] walks down the resulting conjunction
    exactly like [try_ih_conjuncts] does mid-proof, until it finds the
    one conjunct matching the current goal. *)
Ltac finish_from_conjunct Hc :=
  first
    [ eapply Hc; eassumption
    | eapply (proj1 Hc); eassumption
    | finish_from_conjunct (proj2 Hc) ].

Ltac animation_soundness_project joint_lemma :=
  intros;
  match goal with
  | Hanim : ?F ?n0 _ = Success _ _ |- _ => finish_from_conjunct (joint_lemma n0)
  end.

(* ==================================================================== *)
(** ** Validation 1: [add] -- self-recursion only, no guards, no
    cross-relation calls. Copied verbatim from TestSoundnessAdd.v. *)
(* ==================================================================== *)

Module AddValidation.

Inductive add : nat -> nat -> nat -> Prop :=
| add_zero : forall (x : nat), add 0 x x
| add_succ : forall (v0 x v1 : nat), add v0 x v1 -> add (S v0) x (S v1).

MetaRocq Run (animate_inductive <?add?> [("add", ([0;1], [2]))] 100).

(** A bundle of exactly one relation: no [/\] to split at all, and
    [animation_soundness_proof_joint] -- unlike the old depth-[Fixpoint]
    design -- introduces no artificial bound that a separate wrapper
    [Theorem] would need to strip. So there's nothing a second
    declaration could add; the one, final, user-facing statement is
    exactly [animation_soundness_proof_joint]'s own goal shape, proved
    directly, no [_aux] needed. *)
Theorem add_soundness : forall (n v0 x v1 : nat),
  addAnimatedTopFn n (Success (nat * nat) (v0, x)) = Success nat v1 ->
  add v0 x v1.
Proof. animation_soundness_proof_joint. Qed.

End AddValidation.

(* ==================================================================== *)
(** ** Validation 2: [stack_step] -- pure pattern-matching, five clauses,
    ZERO recursive premises. A bundle of one, non-recursive relation is
    still just [animation_soundness_proof_joint]: the well-founded [IH]
    it introduces simply goes unused (nothing of shape [_ = Success _ _]
    besides [Hanim] itself exists for [close_clause_joint]'s loop to
    touch). Originally copied verbatim from TestSoundnessStack.v. *)
(* ==================================================================== *)

Module StackValidation.

Definition total_map (A : Type) := string -> A.
Definition state := total_map nat.

Inductive sinstr : Type :=
| SPush (n : nat)
| SLoad (x : string)
| SPlus
| SMinus
| SMult.

Fixpoint decEqsinstr : forall (t1 t2 : sinstr), {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality. decide equality. decide equality. decide equality.
Defined.

Definition eqFnsinstr (t1 t2 : sinstr) : bool :=
  if decEqsinstr t1 t2 then true else false.

Definition stack := list nat.
Definition prog  := list sinstr.

Inductive stack_step : state -> list sinstr * list nat -> list sinstr * list nat -> Prop :=
| SS_Push  : forall st stk n p ps0 ps1,
    ps0 = (SPush n :: p, stk) /\ ps1 = (p, n :: stk)
    -> stack_step st ps0 ps1
| SS_Load  : forall st stk i p ps0 ps1,
    ps0 = (SLoad i :: p, stk) /\ ps1 = (p, (st) i :: stk)
    -> stack_step st ps0 ps1
| SS_Plus  : forall st stk n m p ps0 ps1,
    ps0 = (SPlus :: p, n :: m :: stk) /\ ps1 = (p, (m + n) :: stk)
    -> stack_step st ps0 ps1
| SS_Minus : forall st stk n m p ps0 ps1,
    ps0 = (SMinus :: p, n :: m :: stk) /\ ps1 = (p, (m - n) :: stk)
    -> stack_step st ps0 ps1
| SS_Mult  : forall st stk n m p ps0 ps1,
    ps0 = (SMult :: p, n :: m :: stk) /\ ps1 = (p, (m * n) :: stk)
    -> stack_step st ps0 ps1 .

MetaRocq Run (animate_inductive <? stack_step ?>
  [("stack_step", ([0;1], [2]))] 200).

(** Same reasoning as [add_soundness] -- a one-relation bundle has no
    artificial bound to strip, so no [_aux] is needed; see the comment
    there. *)
Theorem stack_step_soundness :
  forall (n : nat) (st : state) (p_list : list sinstr) (stk : list nat)
         (ps1 : list sinstr * list nat),
  stack_stepAnimatedTopFn n
    (Success (state * (list sinstr * list nat)) (st, (p_list, stk))) =
  Success (list sinstr * list nat) ps1 ->
  stack_step st (p_list, stk) ps1.
Proof. animation_soundness_proof_joint. Qed.

End StackValidation.

(* ==================================================================== *)
(** ** Validation 3: [typing]/[lookup] (STLC) -- the hard case: boolean
    [eqFn] guards ([TAdd]/[TApp]), same-relation recursion ([TAdd]/[TAbs]/
    [TApp]), AND a cross-relation call into [lookup] ([TVar]). [lookup]
    has a standalone top-level name (bundled with [typing] into one
    mutual fix block by MetaRocq, since both were fed to one
    [animate_inductive] call, and the engine now emits a separate
    [AnimatedTopFn] per relation in that block -- see [emit_aux_topfns]
    in AnimationEngine.v). [typing]'s and [lookup]'s joint soundness
    [Lemma] below handles EVERY clause, [TVar] included, with zero
    per-clause or per-relation code: [animation_soundness_proof_joint]
    doesn't need to know in advance which relation a recursive call
    hypothesis belongs to, it just tries each conjunct. Originally
    copied verbatim from TestSoundnessSTLC.v. *)
(* ==================================================================== *)

Module STLCValidation.

Inductive ty : Type :=
| TBool : ty
| TArrow : ty -> ty -> ty.

Inductive tm : Type :=
| tcon : nat -> tm
| tadd : tm -> tm -> tm
| tvar : nat -> tm
| tapp : tm -> tm -> tm
| tabs : ty -> tm -> tm.

Fixpoint decEqTy : forall (t1 t2 : ty), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Defined.

Fixpoint decEqTm : forall (t1 t2 : tm), {t1 = t2} + {t1 <> t2}.
Proof. decide equality. decide equality. decide equality. decide equality. Defined.

Definition eqFnty (t1 t2 : ty) : bool :=
  if decEqTy t1 t2 then true else false.

Definition eqFntm (t1 t2 : tm) : bool :=
  if decEqTm t1 t2 then true else false.

Inductive lookup : list ty -> nat -> ty -> Prop :=
| LookupHere : forall (t : ty) (cxt : list ty), lookup (t :: cxt) 0 t
| LookupThere : forall (m : nat) (t t' : ty) (cxt : list ty),
    lookup cxt m t -> lookup (t' :: cxt) (S m) t.

Inductive typing : list ty -> tm -> ty -> Prop :=
| TCon : forall (n : nat) (cxt : list ty), typing cxt (tcon n) TBool

| TAdd : forall (e1 e2 : tm) (cxt : list ty),
    typing cxt e1 TBool /\ typing cxt e2 TBool ->
    typing cxt (tadd e1 e2) TBool

| TAbs : forall (e : tm) (t1 t2 : ty) (cxt cxt' : list ty),
    cxt' = t1 :: cxt /\ typing cxt' e t2 ->
    typing cxt (tabs t1 e) (TArrow t1 t2)

| TVar : forall (j : nat) (t : ty) (cxt : list ty),
    lookup cxt j t -> typing cxt (tvar j) t

| TApp : forall (e1 e2 : tm) (t1 t2 : ty) (cxt : list ty),
    typing cxt e2 t1 /\ typing cxt e1 (TArrow t1 t2) ->
    typing cxt (tapp e1 e2) t2.

MetaRocq Run (animate_inductive <?typing?> [("typing", ([0;1], [2])); ("lookup", ([0;1], [2]))] 100).

(** No [eqFnty_sound] lemma needed: [resolve_eqfn_guards] discharges the
    [eqFnty TBool t = true]-shaped guards in [TAdd]/[TApp]'s clauses
    inline via [eqfn_sound_inline], the moment they're encountered. *)

(** [typing] and [lookup] were fed to the SAME [animate_inductive] call
    above, so they're one bundle: ONE joint [Lemma], one conjunct each,
    proved once by [animation_soundness_proof_joint] -- regardless of
    the fact that [typing] calls [lookup] but not vice versa (the tactic
    never needs to know that; it would look identical if the dependency
    went both ways). Each relation's own [Theorem] then just projects
    its conjunct back out. *)
Lemma typing_lookup_soundness_aux : forall (n : nat),
  (forall (cxt : list ty) (e : tm) (out : ty),
    typingAnimatedTopFn n (Success (list ty * tm) (cxt, e)) = Success ty out ->
    typing cxt e out)
  /\
  (forall (cxt : list ty) (j : nat) (out : ty),
    lookupAnimatedTopFn n (Success (list ty * nat) (cxt, j)) = Success ty out ->
    lookup cxt j out).
Proof. animation_soundness_proof_joint. Qed.

Theorem typing_soundness : forall (n : nat) (cxt : list ty) (e : tm) (out : ty),
  typingAnimatedTopFn n (Success (list ty * tm) (cxt, e)) = Success ty out ->
  typing cxt e out.
Proof. animation_soundness_project typing_lookup_soundness_aux. Qed.

Theorem lookup_soundness : forall (n : nat) (cxt : list ty) (j : nat) (out : ty),
  lookupAnimatedTopFn n (Success (list ty * nat) (cxt, j)) = Success ty out ->
  lookup cxt j out.
Proof. animation_soundness_project typing_lookup_soundness_aux. Qed.

End STLCValidation.

(* ==================================================================== *)
(** ** Validation 4: list relations ([append]/[length_rel]/[suffix]/
    [rev_acc], from TestList.v) -- all four are self-recursive only, no
    [eqFn] guards, no cross-relation calls, each its own single-relation
    [modes] bundle. Every one collapses to the exact same one-line
    pattern as [add]. *)
(* ==================================================================== *)

Module ListValidation.

Inductive append : list nat -> list nat -> list nat -> Prop :=
| appendNil : forall (l2 : list nat), append [] l2 l2
| appendCons : forall (w : nat) (l2 l3 l4 : list nat),
    append l2 l3 l4 -> append (w :: l2) l3 (w :: l4).

MetaRocq Run (animate_inductive <?append?> [("append", ([0;1], [2]))] 100).

Theorem append_soundness : forall (n : nat) (l1 l2 l3 : list nat),
  appendAnimatedTopFn n (Success (list nat * list nat) (l1, l2)) = Success (list nat) l3 ->
  append l1 l2 l3.
Proof. animation_soundness_proof_joint. Qed.

Inductive length_rel : list nat -> nat -> Prop :=
| length_nil : length_rel [] 0
| length_cons : forall (w : nat) (l : list nat) (n : nat),
    length_rel l n -> length_rel (w :: l) (S n).

MetaRocq Run (animate_inductive <?length_rel?> [("length_rel", ([0], [1]))] 100).

Theorem length_rel_soundness : forall (n : nat) (l : list nat) (len : nat),
  length_relAnimatedTopFn n (Success (list nat) l) = Success nat len ->
  length_rel l len.
Proof. animation_soundness_proof_joint. Qed.

Inductive suffix : list nat -> list nat -> list nat -> Prop :=
| suffixNil : forall (l2 : list nat), suffix [] l2 l2
| suffixCons : forall (w : nat) (l2 l3 l4 : list nat),
    suffix l2 l3 l4 -> suffix (w :: l2) l3 (w :: l4).

MetaRocq Run (animate_inductive <?suffix?> [("suffix", ([0;2], [1]))] 100).

Theorem suffix_soundness : forall (n : nat) (pre full suf : list nat),
  suffixAnimatedTopFn n (Success (list nat * list nat) (pre, full)) = Success (list nat) suf ->
  suffix pre suf full.
Proof. animation_soundness_proof_joint. Qed.

Inductive rev_acc : list nat -> list nat -> list nat -> Prop :=
| rev_nil : forall (acc : list nat), rev_acc [] acc acc
| rev_cons : forall (w : nat) (l acc res : list nat),
    rev_acc l (w :: acc) res -> rev_acc (w :: l) acc res.

MetaRocq Run (animate_inductive <?rev_acc?> [("rev_acc", ([0;1], [2]))] 100).

Theorem rev_acc_soundness : forall (n : nat) (l acc res : list nat),
  rev_accAnimatedTopFn n (Success (list nat * list nat) (l, acc)) = Success (list nat) res ->
  rev_acc l acc res.
Proof. animation_soundness_proof_joint. Qed.

End ListValidation.

(* ==================================================================== *)
(** ** Validation 5: [lam_step] (untyped lambda calculus CBN step, from
    TestLambdaCalc.v) -- one base case with no recursion ([LS_Beta]),
    one self-recursive case ([LS_App]), single-relation bundle. *)
(* ==================================================================== *)

Module LambdaCalcValidation.

Inductive lam_tm : Type :=
| lvar : nat -> lam_tm
| lapp : lam_tm -> lam_tm -> lam_tm
| labs : lam_tm -> lam_tm.

Fixpoint lshift (d c : nat) (t : lam_tm) : lam_tm :=
  match t with
  | lvar n => if Nat.leb c n then lvar (n + d) else lvar n
  | lapp t1 t2 => lapp (lshift d c t1) (lshift d c t2)
  | labs t1 => labs (lshift d (S c) t1)
  end.

Fixpoint lsubst (n : nat) (s : lam_tm) (t : lam_tm) : lam_tm :=
  match t with
  | lvar m => if Nat.eqb m n then s else t
  | lapp t1 t2 => lapp (lsubst n s t1) (lsubst n s t2)
  | labs t1 => labs (lsubst (S n) (lshift 1 0 s) t1)
  end.

Inductive lam_step : lam_tm -> lam_tm -> Prop :=
| LS_Beta : forall (t1 t2 : lam_tm),
    lam_step (lapp (labs t1) t2) (lsubst 0 t2 t1)
| LS_App : forall (e1 e1' e2 : lam_tm),
    lam_step e1 e1' ->
    lam_step (lapp e1 e2) (lapp e1' e2).

MetaRocq Run (animate_inductive <?lam_step?> [("lam_step", ([0], [1]))] 200).

Theorem lam_step_soundness : forall (n : nat) (t1 t2 : lam_tm),
  lam_stepAnimatedTopFn n (Success lam_tm t1) = Success lam_tm t2 ->
  lam_step t1 t2.
Proof. animation_soundness_proof_joint. Qed.

End LambdaCalcValidation.

(* ==================================================================== *)
(** ** Validation 6+: the remaining examples from TestNat.v, in file
    order. [add]/[mul] are plain self-recursive -- skipping [add] here
    since it's identical to [AddValidation.add] above. *)
(* ==================================================================== *)

Module NatMiscValidation.

Inductive tripleIn : nat -> nat -> bool -> nat -> nat -> bool -> Prop :=
| tInC : forall a b c, tripleIn a b c a b c.

MetaRocq Run (animate_inductive <?tripleIn?> [("tripleIn", ([0;1;2], [3;4;5]))] 200).

Theorem tripleIn_soundness : forall (n : nat) (a b : nat) (c : bool) (a' b' : nat) (c' : bool),
  tripleInAnimatedTopFn n (Success (nat * (nat * bool)) (a, (b, c))) =
  Success (nat * (nat * bool)) (a', (b', c')) ->
  tripleIn a b c a' b' c'.
Proof. animation_soundness_proof_joint. Qed.

(** [isGood2] bundle: empty INPUT mode (all three relations take a bare
    [bool true] "go" trigger, no real data in). *)
Inductive isGoodEmptyIn : list nat -> nat -> Prop :=
| zeroCEmptyIn : isGoodEmptyIn [] 0.

Inductive isGoodEmptyIn' : list nat -> nat -> Prop :=
| zeroCEmptyIn' : isGoodEmptyIn' [] 1.

Inductive isGood2 : list nat -> nat -> Prop :=
| isG2 : forall n l, isGoodEmptyIn' l n /\ isGoodEmptyIn l n -> isGood2 l n.

MetaRocq Run (animate_inductive <? isGood2 ?>
  [("isGood2", ([], [0;1]));
   ("isGoodEmptyIn", ([], [0;1]));
   ("isGoodEmptyIn'", ([], [0;1]))] 100).

Lemma isGood2_bundle_soundness_aux : forall (n : nat),
  (forall (l : list nat) (m : nat),
    isGood2AnimatedTopFn n (Success bool true) = Success (list nat * nat) (l, m) -> isGood2 l m)
  /\
  (forall (l : list nat) (m : nat),
    isGoodEmptyInAnimatedTopFn n (Success bool true) = Success (list nat * nat) (l, m) -> isGoodEmptyIn l m)
  /\
  (forall (l : list nat) (m : nat),
    isGoodEmptyIn'AnimatedTopFn n (Success bool true) = Success (list nat * nat) (l, m) -> isGoodEmptyIn' l m).
Proof. animation_soundness_proof_joint. Qed.

(** [isGood3] bundle: empty OUTPUT mode (all three just return a bare
    success/fail [bool], no real data out). *)
Inductive isGoodEmptyIn3 : list nat -> nat -> Prop :=
| zeroCEmptyIn3 : isGoodEmptyIn3 [] 0.

Inductive isGoodEmptyIn'3 : list nat -> nat -> Prop :=
| zeroCEmptyIn'3 : isGoodEmptyIn'3 [] 0.

Inductive isGood3 : list nat -> nat -> Prop :=
| isG3 : forall n l, isGoodEmptyIn'3 l n /\ isGoodEmptyIn3 l n -> isGood3 l n.

MetaRocq Run (animate_inductive <? isGood3 ?>
  [("isGood3", ([0;1], []));
   ("isGoodEmptyIn3", ([0;1], []));
   ("isGoodEmptyIn'3", ([0;1], []))] 100).

Lemma isGood3_bundle_soundness_aux : forall (n : nat),
  (forall (l : list nat) (m : nat),
    isGood3AnimatedTopFn n (Success (list nat * nat) (l, m)) = Success bool true -> isGood3 l m)
  /\
  (forall (l : list nat) (m : nat),
    isGoodEmptyIn3AnimatedTopFn n (Success (list nat * nat) (l, m)) = Success bool true -> isGoodEmptyIn3 l m)
  /\
  (forall (l : list nat) (m : nat),
    isGoodEmptyIn'3AnimatedTopFn n (Success (list nat * nat) (l, m)) = Success bool true -> isGoodEmptyIn'3 l m).
Proof. animation_soundness_proof_joint. Qed.

(** [isGood]/[isGood'] bundle: reversed usual mode (input is position 1,
    output is position 0). *)
Inductive isGood' : list nat -> nat -> Prop :=
| zeroC : isGood' [] 0.

Inductive isGood : list nat -> nat -> Prop :=
| isG : forall n l, isGood' l n -> isGood l n.

MetaRocq Run (animate_inductive <? isGood ?>
  [("isGood", ([1], [0])); ("isGood'", ([1], [0]))] 100).

Lemma isGood_bundle_soundness_aux : forall (n : nat),
  (forall (m : nat) (l : list nat), isGoodAnimatedTopFn n (Success nat m) = Success (list nat) l -> isGood l m)
  /\
  (forall (m : nat) (l : list nat), isGood'AnimatedTopFn n (Success nat m) = Success (list nat) l -> isGood' l m).
Proof. animation_soundness_proof_joint. Qed.

Inductive mul : nat -> nat -> nat -> Prop :=
| mul_zero : forall (n : nat), mul 0 n 0
| mul_succ : forall (m n k : nat), mul m n k -> mul (S m) n (n + k).

MetaRocq Run (animate_inductive <?mul?> [("mul", ([0;1], [2]))] 100).

Theorem mul_soundness : forall (n : nat) (m k p : nat),
  mulAnimatedTopFn n (Success (nat * nat) (m, k)) = Success nat p ->
  mul m k p.
Proof. animation_soundness_proof_joint. Qed.

Inductive leq : nat -> nat -> bool -> Prop :=
| leq_zero : forall (n : nat), leq 0 n true
| leq_succ : forall (m n : nat) (b : bool), leq m n b -> leq (S m) (S n) b
| leq_fail : forall (m : nat), leq (S m) 0 false.

MetaRocq Run (animate_inductive <?leq?> [("leq", ([0;1], [2]))] 100).

Theorem leq_soundness : forall (n : nat) (m k : nat) (b : bool),
  leqAnimatedTopFn n (Success (nat * nat) (m, k)) = Success bool b ->
  leq m k b.
Proof. animation_soundness_proof_joint. Qed.

End NatMiscValidation.

(* ==================================================================== *)
(** ** Validation 7: [even]/[odd] -- a GENUINE CYCLE in one mutual
    [with] block ([even] calls [odd] and vice versa), not an acyclic DAG
    like [typing]/[lookup]. Exactly the case the joint well-founded-
    induction design was built for: both conjuncts share one [IH]
    covering BOTH relations at every smaller fuel, so neither needs to
    be "finished" before the other. *)
(* ==================================================================== *)

Module ParityValidation.

Inductive even : nat -> bool -> Prop :=
| even0 : even 0 true
| evenSucc : forall (w : nat), odd w true -> even (S w) true
with odd : nat -> bool -> Prop :=
| oddSucc : forall (w : nat), even w true -> odd (S w) true.

MetaRocq Run (animate_inductive <?even?> [("even", ([0], [1])); ("odd", ([0], [1]))] 100).

(** Previously blocked by an [AnimationEngine.v] gap: [emit_aux_topfns]'s
    emission loop used to be bounded by [length knLst], and [knLst]
    (from [infer_aux_knames]) never discovered [odd] at all, since a
    cross-reference WITHIN a native mutual [with] block is a bare
    [tRel], not the [tInd] [infer_aux_knames] scans for. Fixed by
    driving the loop from [length defs] instead (the real arm count,
    regardless of how each arm got into [defs]) -- see [emit_aux_topfns]
    in AnimationEngine.v. Confirmed fixed: [oddAnimatedTopFn] now exists
    standalone, and this is a one-liner like every other bundle. *)
Lemma even_odd_soundness_aux : forall (n : nat),
  (forall (w : nat) (b : bool), evenAnimatedTopFn n (Success nat w) = Success bool b -> even w b)
  /\
  (forall (w : nat) (b : bool), oddAnimatedTopFn n (Success nat w) = Success bool b -> odd w b).
Proof. animation_soundness_proof_joint. Qed.

End ParityValidation.

(* ==================================================================== *)
(** ** Validation 7b: [tripled_parity]/[triple2]/[evn4]/[od4] -- a
    standalone relation ([triple2]) MIXED with a native mutual pair
    ([evn4]/[od4]) in one bundle. Previously blocked a SECOND, nastier
    way: [od4] sneaking into [defs] via [evn4]'s own native-mutual
    quoting used to shift every later index, so the old
    [length knLst]-bounded loop undershot and [triple2] -- an ordinary,
    otherwise trivially provable relation with nothing to do with any
    of this -- never got a name at all. Same engine fix resolves both
    at once: driving the loop from [length defs] reaches every real
    arm regardless of how it got there. *)
(* ==================================================================== *)

Module MixedBlocksSoloValidation.

Inductive triple2 : nat -> nat -> Prop :=
| t2_zero : triple2 0 0
| t2_succ : forall n m, triple2 n m -> triple2 (S n) (S (S (S m))).

Inductive evn4 : nat -> bool -> Prop :=
| evn4_zero : evn4 0 true
| evn4_succ : forall n, od4 n true -> evn4 (S n) true
with od4 : nat -> bool -> Prop :=
| od4_succ : forall n, evn4 n true -> od4 (S n) true.

Inductive tripled_parity : nat -> (nat * bool) -> Prop :=
| tp_rule : forall n t b,
    triple2 n t /\ evn4 t b -> tripled_parity n (t, b).

MetaRocq Run (animate_inductive <?tripled_parity?>
  [("tripled_parity", ([0], [1]));
   ("triple2",        ([0], [1]));
   ("evn4",           ([0], [1]));
   ("od4",            ([0], [1]))] 50).

Lemma tripled_parity_bundle_soundness_aux : forall (n : nat),
  (forall (a : nat) (t : nat) (b : bool),
    tripled_parityAnimatedTopFn n (Success nat a) = Success (nat * bool) (t, b) ->
    tripled_parity a (t, b))
  /\
  (forall (a c : nat), triple2AnimatedTopFn n (Success nat a) = Success nat c -> triple2 a c)
  /\
  (forall (w : nat) (b : bool), evn4AnimatedTopFn n (Success nat w) = Success bool b -> evn4 w b)
  /\
  (forall (w : nat) (b : bool), od4AnimatedTopFn n (Success nat w) = Success bool b -> od4 w b).
Proof. animation_soundness_proof_joint. Qed.

End MixedBlocksSoloValidation.

(* ==================================================================== *)
(** ** Validation 7c: [even_ident]/[evn5]/[od5]/[val_check]/[val_helper]
    -- TWO SEPARATE native mutual blocks ([evn5]/[od5], and
    [even_ident]/[val_check]/[val_helper] -- note [even_ident] is
    natively mutual with its OWN two auxiliary relations) combined into
    ONE 5-relation animation bundle. Same engine fix; same one-liner. *)
(* ==================================================================== *)

Module TwoMutualBlocksValidation.

Inductive evn5 : nat -> bool -> Prop :=
| evn5_zero : evn5 0 true
| evn5_succ : forall n, od5 n true -> evn5 (S n) true
with od5 : nat -> bool -> Prop :=
| od5_succ : forall n, evn5 n true -> od5 (S n) true.

Inductive even_ident : nat -> nat -> Prop :=
| ei_rule : forall n m,
    evn5 n true /\ val_check n m -> even_ident n m
with val_check : nat -> nat -> Prop :=
| vc_zero : val_check 0 0
| vc_succ : forall n m, val_helper n m -> val_check (S n) (S m)
with val_helper : nat -> nat -> Prop :=
| vh_zero : val_helper 0 0
| vh_succ : forall n m, val_check n m -> val_helper (S n) (S m).

MetaRocq Run (animate_inductive <?even_ident?>
  [("even_ident",  ([0], [1]));
   ("evn5",        ([0], [1]));
   ("od5",         ([0], [1]));
   ("val_check",   ([0], [1]));
   ("val_helper",  ([0], [1]))] 30).

Lemma even_ident_bundle_soundness_aux : forall (n : nat),
  (forall (a c : nat), even_identAnimatedTopFn n (Success nat a) = Success nat c -> even_ident a c)
  /\
  (forall (w : nat) (b : bool), evn5AnimatedTopFn n (Success nat w) = Success bool b -> evn5 w b)
  /\
  (forall (w : nat) (b : bool), od5AnimatedTopFn n (Success nat w) = Success bool b -> od5 w b)
  /\
  (forall (a c : nat), val_checkAnimatedTopFn n (Success nat a) = Success nat c -> val_check a c)
  /\
  (forall (a c : nat), val_helperAnimatedTopFn n (Success nat a) = Success nat c -> val_helper a c).
Proof. animation_soundness_proof_joint. Qed.

End TwoMutualBlocksValidation.

(* ==================================================================== *)
(** ** Validation 8: [patGuard]/[patGuard']/[patGuardFnApp] -- ground
    PROPOSITIONAL equality guards (literal [=], not a boolean [eqFn])
    on a custom type [newTp], and one on a defined function applied to
    a variable. Each is its own single-relation, non-recursive bundle. *)
(* ==================================================================== *)

Module PatternGuardValidation.

Inductive newTp : Type :=
| nulCon : newTp
| unaCon : nat -> newTp -> newTp.

Inductive patGuard : newTp -> newTp -> Prop :=
| checkEq : forall w u, u = nulCon /\ unaCon 5 (unaCon 6 nulCon) = w /\ unaCon 5 nulCon = unaCon 5 nulCon -> patGuard w u.

MetaRocq Run (animate_inductive <?patGuard?>
  [("patGuard", ([0;1], []))] 100).

Theorem patGuard_soundness : forall (n : nat) (w u : newTp),
  patGuardAnimatedTopFn n (Success (newTp * newTp) (w, u)) = Success bool true ->
  patGuard w u.
Proof. animation_soundness_proof_joint. Qed.

Inductive patGuard' : newTp -> newTp -> Prop :=
| checkEq' : forall w u, u = nulCon /\ unaCon 5 (unaCon 6 nulCon) = w /\ unaCon 5 nulCon = nulCon -> patGuard' w u.

MetaRocq Run (animate_inductive <?patGuard'?>
  [("patGuard'", ([0;1], []))] 100).

Theorem patGuard'_soundness : forall (n : nat) (w u : newTp),
  patGuard'AnimatedTopFn n (Success (newTp * newTp) (w, u)) = Success bool true ->
  patGuard' w u.
Proof. animation_soundness_proof_joint. Qed.

Definition wrap_nat (n : nat) : newTp :=
  match n with
  | 0   => nulCon
  | S k => unaCon k nulCon
  end.

Inductive patGuardFnApp : nat -> nat -> Prop :=
| pgfa_rule : forall n m, nulCon = wrap_nat n /\ wrap_nat m = nulCon -> patGuardFnApp n m.

MetaRocq Run (animate_inductive <?patGuardFnApp?>
  [("patGuardFnApp", ([0;1], []))] 100).

Theorem patGuardFnApp_soundness : forall (n0 : nat) (n m : nat),
  patGuardFnAppAnimatedTopFn n0 (Success (nat * nat) (n, m)) = Success bool true ->
  patGuardFnApp n m.
Proof. animation_soundness_proof_joint. Qed.

End PatternGuardValidation.

(* ==================================================================== *)
(** ** Validation 10: [rel]/[rel2] -- another native mutual [with] pair,
    but LOGICALLY ACYCLIC this time ([rel] calls [rel2], [rel2] never
    calls back). Confirms the engine gap was about the native [with]
    DECLARATION SYNTAX, not about cyclic dependency: this one has no
    cycle at all, yet [rel2AnimatedTopFn] was equally missing before the
    [emit_aux_topfns] fix, for the exact same [tRel]-vs-[tInd] reason. *)
(* ==================================================================== *)

Module ClashRelNameValidation.

Inductive rel : nat -> nat -> Prop :=
| x : forall v0 v1, rel2 v0 v1 -> rel v0 v1
with rel2 : nat -> nat -> Prop :=
| x_base' : rel2 0 0
| x_step' : forall (x v1 : nat), rel2 x v1 -> rel2 (S x) (S v1).

MetaRocq Run (animate_inductive <?rel?> [("rel", ([0], [1])); ("rel2", ([0], [1]))] 200).

Lemma rel_bundle_soundness_aux : forall (n : nat),
  (forall (a c : nat), relAnimatedTopFn n (Success nat a) = Success nat c -> rel a c)
  /\
  (forall (a c : nat), rel2AnimatedTopFn n (Success nat a) = Success nat c -> rel2 a c).
Proof. animation_soundness_proof_joint. Qed.

End ClashRelNameValidation.

(* ==================================================================== *)
(** ** Validation 11: [step] (STLC small-step CBV reduction, from
    TestSTLC.v's [STLCStep] module -- missed on the first pass through
    this file, since its [typing]/[lookup] section at the top duplicates
    [STLCValidation] and nothing further was checked). Self-recursive
    only, no cross-relation calls; its outputs are computed directly via
    the auxiliary [subst] function (same pattern as [lam_step]'s
    [lsubst]), not compared against anything, so no new guard shape. *)
(* ==================================================================== *)

Module STLCStepValidation.

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

Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  | tvar y => if String.eqb x y then s else t
  | tabs y T t1 => if String.eqb x y then t else tabs y T (subst x s t1)
  | tapp t1 t2 => tapp (subst x s t1) (subst x s t2)
  | ttrue => ttrue
  | tfalse => tfalse
  | tif t1 t2 t3 => tif (subst x s t1) (subst x s t2) (subst x s t3)
  end.

Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall (z : string) (T : ty) (t w : tm),
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
    step (tif t1 t2 t3) (tif t1' t2 t3).

MetaRocq Run (animate_inductive <?step?> [("step", ([0], [1]))] 100).

Theorem step_soundness : forall (n : nat) (t1 t2 : tm),
  stepAnimatedTopFn n (Success tm t1) = Success tm t2 ->
  step t1 t2.
Proof. animation_soundness_proof_joint. Qed.

End STLCStepValidation.
