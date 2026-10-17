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
Ltac saturate_step H :=
  first
    [ match type of H with
      | context [ match ?x with _ => _ end ] => is_var x; destruct x eqn:?
      end
    | match type of H with
      | context [ match ?call with _ => _ end ] =>
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
    | match type of H with
      | context [ if ?cond then _ else _ ] => destruct cond eqn:?
      end
    ]; cbn beta iota zeta in H.

(** [cbn]/[simpl] without an explicit name list are conservative: they
    won't delta-unfold a clause function whose body would still be stuck
    on free-variable scrutinees afterward (the hand-proofs always named
    the clause function explicitly, e.g. [unfold add_zeroAnimated]). The
    generic tactic can't hard-code that name, but [H]'s own head symbol
    IS that name, so [match type of H with ?F _ _ = _ => unfold F in H
    end] reads it off and unfolds it by reference -- tried at a few
    arities since a clause may take a leading recursive-function
    argument (e.g. [add_succAnimated f m input]) or not
    (e.g. [add_zeroAnimated m input]). *)
Ltac unfold_clause_head H :=
  first
    [ match type of H with ?F _ = _ => unfold F in H end
    | match type of H with ?F _ _ = _ => unfold F in H end
    | match type of H with ?F _ _ _ = _ => unfold F in H end
    | idtac ].

(** These library-level combinator names ARE fixed (not per-relation), so
    unlike the clause function's own name, the generic tactic can just
    hard-code them -- same list as the hand-proofs' [unfold_combinators]. *)
Ltac unfold_combinators_in H :=
  unfold compose_outcome, option_to_result, join_pair, join_unit,
         split_outcome_fst, split_outcome_snd,
         with_default, dispatch_clauses, fuel_error_fn,
         and_outcome_bool, eq_outcome, id_fn in H.

Ltac saturate_clause H :=
  unfold_clause_head H; unfold_combinators_in H; cbn beta iota zeta in H;
  repeat saturate_step H.

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

Ltac finish_success H :=
  resolve_eqfn_guards;
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

Ltac animation_soundness_proof_joint :=
  let n := fresh "n" in
  let IH := fresh "IH" in
  intros n; induction n as [n IH] using lt_wf_ind;
  repeat split;
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
