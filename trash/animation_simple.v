Require Import Coq.Lists.List.
Require Import List.
            
Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.

Require Import utils.
Import MetaCoqNotations.
Open Scope bs.

Fixpoint inNatLst (a : nat) (l : list nat) : bool :=
 match l with
  | nil => false
  | (h :: t) => if (Nat.eqb h a) then true else (inNatLst a t)
 end.

(* a, b designated as input, c d e designated as output *)
Inductive foo : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr : forall a b c d e, (e = b /\ d = c /\ c = a + e) -> foo a b c d e.

MetaCoq Run (tmQuoteInductive <? foo ?> >>= tmPrint).

Definition animate_conjunct
           (c : constructor_body) (conjunct : context_decl) : TemplateMonad named_term :=
  (* t is the MetaCoq term for the conjunct like (e = b /\ d = c /\ c = a + e) *) 
  let t : term := decl_type conjunct in
  (* tl here only works because we assume there is only one, large, nested "and" conjunct *)
  t_named <- DB.undeBruijn' (tl (map (fun arg => binder_name (decl_name arg)) (cstr_args c))) t ;;
  (* now you can work with the named representation, as you can see below: *)
  tmPrint t_named ;;
  ret hole.

Fixpoint collect_conjuncts (cs : list constructor_body) : TemplateMonad (list named_term) :=
  match cs with
  | [] => ret []
  | c :: cs =>
      match cstr_args c with
      | conjunct :: _ =>
          conjunct' <- animate_conjunct c conjunct ;;
          cs' <- collect_conjuncts cs ;;
          ret (conjunct' :: cs')
      | _ => tmFail "No arguments for constructor c"
      end
  end.

Definition animate (kn : kername) : TemplateMonad unit :=
  mut <- tmQuoteInductive kn ;;
  match ind_bodies mut with
  | [ one ] =>
    conjuncts <- collect_conjuncts (ind_ctors one) ;;
    (* there has to be something clever here *)
    ret conjuncts
  | _ => tmFail "Not one type in mutually inductive block."
  end ;;
  ret tt.

MetaCoq Run (animate <? foo ?>).


(* Let clauses in the same order as foo, leads to error since d depends on c but only a b e are known at that point.  
Definition animate1 (a : nat) (b : nat) : list nat :=
 let e := b in
 let d := c in
 let c := a + e in
 [c ; d ; e]. *)

(** Let Clauses rearranged to be in the right order. The RHS of each let clause only contains input vars or previously calculated vars. **)
Definition animate2 (a : nat) (b : nat) : list nat :=
 let e := b in
 let c := a + e in
 let d := c in
 [c ; d ; e].
 
 
(** Aim : turn foo into foo' : | cstr' : forall a b c d e, (e = b /\ c = a + e /\ d = c) -> foo' a b c d e.
Then turn foo' into animate2 by turning conjuncts in premise of foo' to let clauses in the same order. **)

(** Simpler Problem from the perspective of MetaCoq term size, and to avoid conversion between de bruijn indicies and named 
representations for now, given : **)   
 
Parameter a : nat.
Parameter b : nat.
Parameter c : nat.
Parameter d : nat.
Parameter e : nat.

(** Write a function to turn  (e = b /\ d = c /\ c = a + e) into 
Some ((e = b /\c = a + e /\ d = c)) using the greedy algorithm to compute the correct order of the conjuncts. 
Function should fail with a None if no correct order exists **)  




MetaCoq Quote Definition propTerm := (e = b /\ d = c /\ c = a + e).

Print propTerm.



Fixpoint isListSub (l1 l2 : list nat) : bool :=
 match l1 with
  | nil => true
  | (h :: t) => (inNatLst h l2) && (isListSub t l2)
 end. 
 

 
Fixpoint reOrderStep (x : nat) (y : ((list (list nat) × list nat) × list (list nat)) × list (list nat)) 
                             : ((list (list nat) × list nat) × list (list nat)) × list (list nat) :=
 
 match x with
  | 0 => match y with
          | (ic, kv, sc, rc) => ((ic ++ rc), kv, sc, nil)
          end
  | S m => match y with 
            | (nil, kv, sc, rc) => (rc, kv, sc, nil)
            | ((h :: t), kv, sc, rc) => if (isListSub (tl h) kv) then reOrderStep m (t, (kv ++ h), (h :: sc), rc) else reOrderStep m (t, kv, sc, (h :: rc))
            end 
  end.
  
Fixpoint reOrder (m n : nat) (y : ((list (list nat) × list nat) × list (list nat)) × list (list nat)) : ((list (list nat) × list nat) × list (list nat)) × list (list nat)  :=
  match m with 
   | 0 => y
   | S j => reOrder j n (reOrderStep n y)
  end.



Definition lstCheckEmpty {A : Type} (l : list A) : bool :=
  match l with
  | nil => true
  | _ => false
  end.

Definition sortConj (inputClauses : list (list nat)) (inputVars : list nat) : option (list (list nat)) :=
 if lstCheckEmpty (fst (fst (fst (reOrder (length inputClauses) (length inputClauses) (inputClauses, inputVars, nil, nil))))) then 
     Some (snd (fst (reOrder (length inputClauses) (length inputClauses) (inputClauses, inputVars, nil, nil)))) else None.
     
     
     

Compute (sortConj [[1 ; 0] ; [2 ; 1] ; [3 ; 2] ; [4 ; 3 ; 5]] [5 ; 0]).

Compute (sortConj [[4 ; 1] ; [3 ; 2] ; [2 ; 0 ; 4]] [0 ; 1]).

Compute (sortConj [[1 ; 0] ; [2 ; 1] ; [3 ; 2] ; [4 ; 3 ; 5]] [0]).

Parameter partialProg : nat -> nat.
MetaCoq Quote Definition letTerm := (let a := b in partialProg).

Print letTerm.
     
     
     
(** Definition reorderStep (y : (list (list nat) × list nat) × list (list nat)) : (list (list nat) × list nat) × list (list nat) :=
 let inConj := fst (fst y) in
 let knownVars := snd (fst y) in
 let outConj := snd y in
 match inConj with
  | nil => y
  | h :: t => if sublst (tail h outConj) then (t, (knownVars ++ h), h : outConj) else ( Keep list of unanimated conjuncts also... and then after one round 
  bring back as initial parameter.) (total n rounds of which one round is executed by this fn)

Check (1,2,3).

(** Definition listUnion (l1 l2 : list nat) : list nat :=
 l1 ++ l2.**)
  
(** Fixpoint reorderStep' (y : ((list (list nat) × list nat) × list (list nat)) × list (list nat)) 
                             : ((list (list nat) × list nat) × list (list nat)) × list (list nat) :=
 match y with 
  | (nil, kv, sc, rc) => (rc, kv, sc, nil)
  | ((h :: t), kv, sc, rc) => if (isListSub (tl h) kv) then reorderStep (t, (listUnion kv (h)), (h :: sc), rc) else reorderStep (t, kv, sc, (h :: rc))
 end. **) 
 

(** Check nil.
Check tl. Check length. **) 

(** Fixpoint inNatLst' (a : nat) (l : list nat) : bool.
induction l.
+ apply (inNatLst') in a.
++ apply a.
++ apply nil.
+ apply 
 match l with
  | nil => false
  | (h :: t) => if (Nat.eqb h a) then true else (inNatLst a t)
 end. **)
 
  
 
    
 