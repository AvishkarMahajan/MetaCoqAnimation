(** * HoleyResult: Typed holes for animation output
    Provides [HList] (heterogeneous list indexed by [list Type]) and
    [HoleyResult T] (a value of type [T] with zero or more typed holes).
    Push functions in [coIndPreProcSigma] return [HoleyResult T] so that
    the output of [AnimatedTopFn] carries explicit, distinct, typed holes
    wherever the animation hit an [undefined'] or animation constructor. *)

From Stdlib Require Import List.
Import ListNotations.

(* ------------------------------------------------------------------ *)
(** ** Heterogeneous lists *)

Inductive HList : list Type -> Type :=
| HNil  : HList []
| HCons : forall (T : Type) (Ts : list Type), T -> HList Ts -> HList (T :: Ts).

Arguments HCons {T Ts} _ _.

Definition hlist_head {T : Type} {Ts : list Type} (hl : HList (T :: Ts)) : T :=
  match hl with HCons h _ => h end.

Definition hlist_tail {T : Type} {Ts : list Type} (hl : HList (T :: Ts)) : HList Ts :=
  match hl with HCons _ t => t end.

(** Split a heterogeneous list at a prefix of known length.
    [hlist_split l1 hl] where [hl : HList (l1 ++ l2)] returns
    [(hl1, hl2)] with [hl1 : HList l1] and [hl2 : HList l2]. *)
Fixpoint hlist_split {l2 : list Type} (l1 : list Type)
    (hl : HList (l1 ++ l2)) : HList l1 * HList l2 :=
  match l1 as l1' return HList (l1' ++ l2) -> HList l1' * HList l2 with
  | []      => fun hl' => (HNil, hl')
  | T :: Ts => fun hl' =>
      let h    := hlist_head hl' in
      let rest := hlist_tail hl' in
      let '(hl1, hl2) := hlist_split Ts rest in
      (HCons h hl1, hl2)
  end hl.

(* ------------------------------------------------------------------ *)
(** ** Holey results *)

(** A value of type [T] whose [undefined'] positions have been replaced
    by typed holes.  The hole types are existentially quantified as
    [ht : list Type]; the caller supplies a [HList ht] to fill them. *)
Definition HoleyResult (T : Type) : Type :=
  { ht : list Type & HList ht -> T }.

(** Wrap a concrete value with no holes. *)
Definition hr_pure (T : Type) (val : T) : HoleyResult T :=
  existT _ [] (fun _ => val).

(** A single hole of type [T]. *)
Definition hr_hole (T : Type) : HoleyResult T :=
  existT _ [T] (fun hl => hlist_head hl).

(** Map a function over a holey result (no new holes introduced). *)
Definition hr_map (A B : Type) (f : A -> B) (r : HoleyResult A) : HoleyResult B :=
  existT _ (projT1 r) (fun hl => f (projT2 r hl)).

(** Applicative composition: apply a holey function to a holey argument.
    Holes from [rf] come before holes from [ra] in the combined list. *)
Definition hr_ap (A B : Type) (rf : HoleyResult (A -> B)) (ra : HoleyResult A)
    : HoleyResult B :=
  let hta := projT1 rf in
  let htb := projT1 ra in
  existT _ (hta ++ htb) (fun hl =>
    let '(hla, hlb) := hlist_split hta hl in
    projT2 rf hla (projT2 ra hlb)).

(** Pair two holey results into a holey result of their product. *)
Definition hr_pair (A B : Type) (ra : HoleyResult A) (rb : HoleyResult B)
    : HoleyResult (A * B) :=
  hr_ap B (A * B) (hr_map A (B -> A * B) (@pair A B) ra) rb.
