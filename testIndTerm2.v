Require Import Coq.Lists.List.
Require Import List.
            
Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.
(* Import MetaCoqNotations. *)


  (* Recursive quoting *)
  Notation "<%% x %%>" :=
    ((ltac:(let p y := exact y in run_template_program (tmQuoteRec x) p)))
    (only parsing).
  (* Check <%% nat %%>. *)

  (* Splicing / top level antiquotation *)
  Notation "~( x )" :=
    (ltac:(let p y :=
              let e := eval unfold my_projT2 in (my_projT2 y) in
              exact e in
          run_template_program (tmUnquote x) p))
    (only parsing).
  (* Check (~( <% fun (x : bool) => if x then false else true  %>)). *)
  (* Compute (~(<% fun (x : bool) => if x then false else true %>) false). *)

  (* Name resolution *)
  Notation "<? x ?>" :=
    (ltac:(let p y :=
              match y with
              | tInd {| inductive_mind := ?name |} _ =>
                exact name
              | tConst ?name _ =>
                exact name
              | _ => fail "not a type constructor or definition name" end in
          run_template_program (tmQuote x) p))
    (only parsing).
    
    
Open Scope bs.

Print tApp.

Fixpoint listConcat {A: Type} (l1 : list A) (l2 : list A) : list A :=
 match l1 with
  | nil => l2
  | (h :: t) => listConcat t (h :: l2)
 end.  
Fixpoint listCombine {A : Type} (outerList : list (list A)) : list A :=
 match outerList with
  | nil => nil
  | l1 :: l2 => listConcat l1 (listCombine l2)
  
 end. 

Fixpoint inNatLst (a : nat) (l : list nat) : bool :=
 match l with
  | nil => false
  | (h :: t) => if (Nat.eqb h a) then true else (inNatLst a t)
 end.
 
Fixpoint isListSub (l1 l2 : list nat) : bool :=
 match l1 with
  | nil => true
  | (h :: t) => (inNatLst h l2) && (isListSub t l2)
 end. 

Fixpoint isListSubStr (l1 l2 : list string) : bool. Admitted.
 

(* Definition optionInd {A : Type} (x : (option A)) : bool :=
 match x with
  | Some y => true
  | None => false
 end. *)

(* a, b designated as input, c d e designated as output *)
Inductive foo : nat -> nat -> nat -> nat -> nat -> Prop :=
 | cstr : forall a b c d e, (e = b /\ d = c /\ c = a + e) -> foo a b c d e.


Definition fooTestTerm : term := 
  (tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} [])
   [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
      [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |} [];
       tVar "e"; tVar "b"];
    tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} [])
      [tApp
         (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
            []; tVar "d"; tVar "c"];
       tApp
         (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
         [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
            []; tVar "c"; tApp (tConst (MPfile ["Nat"; "Init"; "Coq"], "add") []) [tVar "a"; tVar "e"]]]]).
            
(* Compute fooTestTerm.*)

Check "d".
Check map.

Print tApp.

Print TemplateMonad.


(* MetaCoq Run (t <- tmUnquoteTyped *) 


Fixpoint getListConj (bigConj : term) : (list term) := (* extract list of conjuncts from big conjunction *)
 match bigConj with
  |(tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "and"); inductive_ind := 0 |} []) ls) => 
         listCombine (map getListConj ls)
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) ls' => 
              [tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} []) ls']
  | _ => nil
 end. 

Definition extractOrderedVars (t : term) : (list string) := (* extract ordered list of vars from conjunct *)
 match t with 
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2] => [str1 ; str2]
 | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (MPfile ["Nat"; "Init"; "Coq"], "add") []) [tVar str2; tVar str3]] => [str1 ; str2 ; str3]
 | _ => nil
 end.
 
MetaCoq Quote Definition letTerm := (fun x => let y := x in y + 1).

Print letTerm.
Check tl.

Parameter resultTerm : term.
Compute ((getListConj fooTestTerm)).

Definition animateOneConjSucc (conj : term) (partialLetfn : term -> term) : option (term -> term) :=
 match conj with
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tVar str2] => Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |} 
            (tVar str2%bs)
            (tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                 inductive_ind := 0
               |} []) ) t))
  
  | tApp (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar str1; tApp (tConst (MPfile ["Nat"; "Init"; "Coq"], "add") []) [tVar str2; tVar str3]] =>
             Some (fun t => partialLetfn ((tLetIn {| binder_name := nNamed str1%bs; binder_relevance := Relevant |}
         (tApp (tConst (MPfile ["Nat"%bs; "Init"%bs; "Coq"%bs], "add"%bs) []) [tVar str2%bs; tVar str3%bs])
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} []) ) t))
     
  
  
  | _ => None
 end.             
               

(* Definition animateOneConjSucc (conj : term) (partialProg : term) : option (term) :=
 match partialProg with 
   | tLambda name type (tLambda name' type' (paritialLetTerm resultTerm)) => 
      Some ((tLambda name type (partialLetTerm (tLambda name' type' ((tLetIn {| binder_name := nNamed "c"%bs; binder_relevance := Relevant |}
         (tApp (tConst (MPfile ["Nat"%bs; "Init"%bs; "Coq"%bs], "add"%bs) []) [tVar "a"%bs; tVar "b"%bs])
         (tInd
            {|
              inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
              inductive_ind := 0
            |} [])) resultTerm)))))
   
   
       
   
   
   
   | _ => None
            
 end. *)
Definition animateOneConj (conj : term) (knownVar : list string) (partialProg : term -> term) : option (list string × (term -> term)) :=
 if (isListSubStr (tl (extractOrderedVars conj)) knownVar) then 
  let t' := (animateOneConjSucc conj partialProg) in
    match t' with
     | Some t'' => Some ((listConcat knownVar (extractOrderedVars conj)), t'')
     | None => None
    end  
    
    else None.  

(* | (h :: t) => if (optionInd (animateOneConj h knownVar partialProg)) then 
                         animateListConj t remConjs (fst (snd (animateOneConj h knownVar partialProg))) n  (snd (snd (animateOneConj h knownVar partialProg))) else 
                         animateListConj t (h :: remConjs) knownVar n partialProg *)

(* recursively apply animateOneConj until
fuel runs out using the bool parameter to check whether animation was succesfull at each iteration *)
 
 

Fixpoint animateListConj (conjs : (list term)) (remConjs : (list term)) (knownVar : list string)
                           (fuel : nat) (partialProg : term -> term) : term -> term :=
 match fuel with 
  | 0 => partialProg
  | S n => match conjs with
           | nil => match remConjs with
                     | nil => partialProg
                     | lst => animateListConj lst nil knownVar n partialProg
                    end  
           | (h :: t) => let res := (animateOneConj h knownVar partialProg) in 
                             match res with
                              | Some res' => animateListConj t remConjs (fst res') n  (snd res')  
                              | None => animateListConj t (h :: remConjs) knownVar n partialProg 
                             end 
                         
           end
 end.                         



Compute ((getListConj fooTestTerm)).

(* (tApp (tConst (MPfile ["Nat"%bs; "Init"%bs; "Coq"%bs], "add"%bs) [])
                  [tVar "b"%bs;
                   tApp
                     (tConstruct
                        {|
                          inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                          inductive_ind := 0
                        |} 1 [])
                     [tConstruct
                        {|
                          inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                          inductive_ind := 0
                        |} 0 []]])


Check eq.

(* Compute <%% e = b %%>.

MetaCoq Run (t <- tmUnquoteTyped (nat -> nat -> Prop) (tApp
          (tInd {| inductive_mind := (MPfile ["Logic"; "Init"; "Coq"], "eq"); inductive_ind := 0 |} [])
          [tInd {| inductive_mind := (MPfile ["Datatypes"; "Init"; "Coq"], "nat"); inductive_ind := 0 |}
             []; tVar "e"; tVar "b"]) ;; tmPrint t). *) *)


                                        
 

Definition genFunTerm (t : term) : term. Admitted.

(* Print TemplateMonad. *)

Definition animate (t : term) : TemplateMonad (nat -> nat -> (list nat)) :=
  f <- @tmUnquoteTyped (nat -> nat -> (list nat)) (genFunTerm t) ;; tmPrint f ;; tmReturn f.


