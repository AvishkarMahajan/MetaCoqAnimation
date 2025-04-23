Require Import Coq.Lists.List.
Require Import List.


Require Import MetaCoq.Template.All.
Import monad_utils.MCMonadNotation.
(* Import MetaCoqNotations. *)

Require Import PeanoNat.
Local Open Scope nat_scope.


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
Compute <? option ?>.

Inductive myType' : Set :=
| mycr1' : nat -> myType'
| mycr2' : nat -> myType'.

Inductive myType : Set :=
| mycr2 : myType' -> nat -> myType
| mycr3 : myType.


Inductive baz' : nat -> nat -> myType -> Prop :=
 | bazCon' : forall (a : nat), forall (x : nat), forall (y : myType), mycr2 (mycr1' a) x = y -> baz' a x y.  (*RHS of equality not v imp*)
 

MetaCoq Quote Recursively Definition baz'Term := baz'.

Print baz'Term. 

Definition extractIndDecl (x : global_decl) : option mutual_inductive_body :=
 match x with
  | InductiveDecl y => Some y
  | _ => None
 end.
 
Parameter error : kername × global_decl.


Parameter error2 : one_inductive_body.

Parameter error3 : constructor_body.






(* Print program.
Print global_env.
Print global_decl. *)



(* Print one_inductive_body. *)


Compute (map extractIndDecl ((map snd ((tl (tl (declarations (fst baz'Term)))))))).

(* Compute (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (tl (tl ((declarations (fst baz'Term))))))))))).*)

(* Compute (option_map cstr_type (option_map (hd error3) (option_map ind_ctors(option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst bazTerm)))))))))). *)

Compute (option_map cstr_args (option_map (hd error3) (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst baz'Term)))))))))).
(* 1st and 3rd computations should have all info needed to build patternmatch fn *)



Definition genVar (n : nat) : string :=
 String.append "v" (string_of_nat (n)).

Fixpoint genVarlst (s : nat) (ls : list term) : list (string × term) :=
 match ls with
  | [] => []
  | h :: t => ((genVar (s + 1)), h) :: (genVarlst (s + 1) t)
 end.   

Definition unfoldConsStep (i : nat) (currTs : list (string × term)) (resolvedTs : list ((string × term) × list string)) 
       (remTs :list (string × term)) : (((nat ×  list (string × term)) × 
                                       list ((string × term) × list string)) × list (string × term))  :=
 match currTs with
 | [] => (i, remTs, resolvedTs, nil)
 (*| (str, ((tApp (tConstruct typeInfo cstrInd ls') args)))  :: t => (i + (length args), t, ((str, (tConstruct typeInfo cstrInd ls'), (map fst (genVarlst i args))) :: resolvedTs), ((genVarlst i args) ++ remTs))*) 
 | (str, (tRel k)) :: t => (i, t, (((str, (tRel k), nil)) :: resolvedTs), remTs)
 | (str, (tVar varStr)) :: t => (i, t, (((str, (tVar varStr ), nil)) :: resolvedTs), remTs)
 (*| (str, (tApp (tInd indType ls') args)) :: t => (i + (length args), t, ((str, (tInd indType ls'), (map fst (genVarlst i args))) :: resolvedTs), ((genVarlst i args) ++ remTs)) *)
 | (str, (tApp func args)) :: t => (i + (length args), t, ((str, func, (map fst (genVarlst i args))) :: resolvedTs), ((genVarlst i args) ++ remTs))
 
 | (str, _) :: t => (i, t, resolvedTs, remTs) 
 end. 
 
Fixpoint unfoldConsStepIter (fuel : nat) (st : (((nat ×  list (string × term)) × 
                                       list ((string × term) × list string)) × list (string × term))) : (((nat ×  list (string × term)) × 
                                       list ((string × term) × list string)) × list (string × term)) :=
  match fuel with
   | 0 => st
   | S m => unfoldConsStepIter m (unfoldConsStep  (fst (fst (fst st))) (snd (fst (fst st))) (snd (fst st)) (snd st))
 end.  

Definition preProcCons (fuel : nat) (t : term) :=
 snd (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], []))).
 
Compute (preProcCons 20 (tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "eq"%bs);
                     inductive_ind := 0
                   |} [])
                [tInd
                   {| inductive_mind := (MPfile ["typeConNest"%bs], "myType"%bs); inductive_ind := 0 |}
                   [];
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["typeConNest"%bs], "myType"%bs); inductive_ind := 0
                      |} 0 [])
                   [tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["typeConNest"%bs], "myType'"%bs);
                           inductive_ind := 0
                         |} 0 []) [tRel 2]; tRel 1]; tRel 0])). 


Compute (rev (preProcCons 20 (
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["typeConNest"%bs], "myType"%bs); inductive_ind := 0
                      |} 0 [])
                   [tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["typeConNest"%bs], "myType'"%bs);
                           inductive_ind := 0
                         |} 0 []) [tVar "a1"%bs]; tVar "a2"%bs]))). 
(* Function :
 fun x => match x with
          | tCon_0_myType v1 v2 =>   match v1 with
                                       | tCon_0_myType' v3 => Some ((v2, v3), ["a2"%bs, "a1"%bs])
                                       | _ => None   
          
          
          | _ => None                    


*)

Definition reduce2 (x : nat) : (option nat) :=
 match x with
  | S m => match m with
            | S n => Some n
            | _ => None
           end
  | _ => None
 end.           




 



Definition preProcConsRem (fuel : nat) (t : term) :=
 snd ((unfoldConsStepIter fuel (0, [("x"%bs, t)], [], []))) ++ snd (fst (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], [])))).  
     
 
Compute (preProcConsRem 20 (
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["typeConNest"%bs], "myType"%bs); inductive_ind := 0
                      |} 0 [])
                   [tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["typeConNest"%bs], "myType'"%bs);
                           inductive_ind := 0
                         |} 0 []) [tRel 2]; tRel 1])).                                                   


(* Print bazTerm.


MetaCoq Quote Definition con3 := (fun x => match x with
                                                | mycr1 a b  =>  Some true
                                                | _ => None
                                               end).
Print con3.


 Goal  (build pattern match branch) :

build function that goes from 

[{|
            decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "eq"%bs);
                     inductive_ind := 0
                   |} [])
                [tInd {| inductive_mind := (MPfile ["Top"%bs], "myType"%bs); inductive_ind := 0 |} [];
                 tApp
                   (tConstruct
                      {| inductive_mind := (MPfile ["Top"%bs], "myType"%bs); inductive_ind := 0 |} 2 [])
                   [tRel 0; tRel 2]; tRel 1]
          |};
          {|
            decl_name := {| binder_name := nNamed "b"%bs; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd
                {|
                  inductive_mind :=
                    (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaCoq"%bs]) "String"%bs, "t"%bs);
                  inductive_ind := 0
                |} []
          |};
          {|
            decl_name := {| binder_name := nNamed "x"%bs; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd {| inductive_mind := (MPfile ["Top"%bs], "myType"%bs); inductive_ind := 0 |} []
          |};
          {|
            decl_name := {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd
                {|
                  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                  inductive_ind := 0
                |} []
          |}] 
          
          TO 
  
  
{|
        bcontext :=
          [{| binder_name := nNamed "b"%bs; binder_relevance := Relevant |};
           {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |}];
        bbody :=
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs);
                 inductive_ind := 0
               |} 0 [])
            [tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "bool"%bs);
                 inductive_ind := 0
               |} [];
             tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "bool"%bs);
                 inductive_ind := 0
               |} 0 []]
      |} 
 *)
      
      
 


Fixpoint genBinderNameList (n : nat) : list (binder_annot name) :=
 match n with 
  | 0 => []
  | S m => {| binder_name := nNamed (String.append "n" (string_of_nat (S m))) ; binder_relevance := Relevant |} :: genBinderNameList m
 end. 



Definition mkNoneBr (cstrArity : nat) (noneVal : term) : branch term :=
  {|
    bcontext :=
    genBinderNameList cstrArity;
    bbody :=
    noneVal
      |}. 
Search (forall A, list A -> nat -> option A).

Definition getDeclName (i : nat) (cxt : list context_decl) : option (binder_annot name) :=
 match (nth_error cxt (i + 1)) with
  | Some r => Some (decl_name r)
  | _ => None
 end. 
(* Compute (nth_error [1;2;3] 0). *)       
 
Fixpoint genBinderannot (ind : list term) (cxt : list context_decl) : option (list (binder_annot name)) :=
 match ind with
  | [] => Some ([])
  | (tRel j :: t) => match (getDeclName j cxt) with
                       | Some b => match (genBinderannot t cxt) with
                                   | Some bs => Some (b :: bs)
                                   | None => None 
                                  end 
                       | _ => None
                       end
  | _ => None 
 end.                         
      
      
      
      
      
      

          
 Definition mkPMBranch (cxt : list context_decl) (someVal : term) : option (branch term) :=
  match cxt with 
   | [] => None
   | (h :: t) => let d := decl_type h in 
                   match d with
                    | tApp
                       (tInd {|
                        inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "eq"%bs);
                        inductive_ind := 0
                                |} [])
                        [tInd typeInfo' [];
                        tApp
                        (tConstruct
                           typeInfo j [])
                           []; tRel k] => Some ({|
                                               bcontext := [];
                                               bbody := someVal  |}) 
                                      
  
                                   
                     | tApp
                       (tInd {|
                        inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "eq"%bs);
                        inductive_ind := 0
                                |} [])
                        [tInd typeInfo' [];
                        tApp
                        (tConstruct
                           typeInfo j [])
                           lst; tRel k]  => match (genBinderannot lst cxt) with 
                                             | Some l' => Some ({|
                                                          bcontext := l' ;
                                                          bbody := someVal  |})
                                             | None => None 
                                            end
                     | _ => None
                    end
   end.

(* Check ({| inductive_mind := (MPfile ["typeCon"%bs], "myType"%bs); inductive_ind := 0 |}). *) 

Definition getPMIndex (cxt : list context_decl)  : option (nat) :=
  match cxt with 
   | [] => None
   | (h :: t) => let d := decl_type h in 
                   match d with
                    | tApp
                       (tInd {|
                        inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "eq"%bs);
                        inductive_ind := 0
                                |} [])
                        [tInd typeInfo' [];
                        tApp
                        (tConstruct
                           typeInfo j [])
                           []; tRel k] => Some j
  
                                   
                     
                     | _ => None
                    end
   end.   
   
Definition mkLambda (scrutineeType : inductive) (scrutineeType' : inductive) (retOpType : term)
                     (scrutineeVar : string) (brs : list (branch term)) : term :=
  tLambda {| binder_name := nNamed scrutineeVar%bs; binder_relevance := Relevant |}
  (tInd scrutineeType [])
  (tCase
     {|
       ci_ind := scrutineeType';
       ci_npar := 0;
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := [];
       pcontext := [{| binder_name := nNamed scrutineeVar%bs; binder_relevance := Relevant |}];
       preturn :=
         retOpType
     |} (tRel 0)                                                                                                        
      brs). (*scrutineeType and scrutineeType' should be same *)                    
                    
                    
                    
                    
       
     
      
      



      
(* AND ANOTHER FUNCTION THAT GOES FROM
 
   {|
            cstr_name := "mycr4"%bs;
            cstr_args :=
              [{|
                 decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type :=
                   tInd
                     {|
                       inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                       inductive_ind := 0
                     |} []
               |};
               {|
                 decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                 decl_body := None;
                 decl_type :=
                   tInd
                     {|
                       inductive_mind :=
                         (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaCoq"%bs]) "String"%bs, "t"%bs);
                       inductive_ind := 0
                     |} []
               |}];
            cstr_indices := [];
            cstr_type :=
              tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                (tInd
                   {|
                     inductive_mind :=
                       (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaCoq"%bs]) "String"%bs, "t"%bs);
                     inductive_ind := 0
                   |} [])
                (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                   (tInd
                      {|
                        inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                        inductive_ind := 0
                      |} []) (tRel 2));
            cstr_arity := 2
          |};
          
          
      TO 
      
      
 {|
        bcontext :=
          [{| binder_name := nNamed "n"%bs; binder_relevance := Relevant |};
           {| binder_name := nNamed "t"%bs; binder_relevance := Relevant |}];
        bbody :=
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs);
                 inductive_ind := 0
               |} 1 [])
            [tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "prod"%bs);
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind :=
                      (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaCoq"%bs]) "String"%bs, "t"%bs);
                    inductive_ind := 0
                  |} [];
                tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                    inductive_ind := 0
                  |} []]]
      |}
      
FOR AN ARBITRARY NO OF CONSTRUCTORS/ PARMETER TYPES. *)




(* Check ([{| binder_name := nNamed "n"%bs; binder_relevance := Relevant |};
           {| binder_name := nNamed "t"%bs; binder_relevance := Relevant |}]).

Check ( {|
        bcontext :=
          [{| binder_name := nNamed "n"%bs; binder_relevance := Relevant |};
           {| binder_name := nNamed "t"%bs; binder_relevance := Relevant |}];
        bbody :=
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "option"%bs);
                 inductive_ind := 0
               |} 1 [])
            [tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "prod"%bs);
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind :=
                      (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaCoq"%bs]) "String"%bs, "t"%bs);
                    inductive_ind := 0
                  |} [];
                tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                    inductive_ind := 0
                  |} []]]
      |}). *)
      
(* Fixpoint genIndex' (s : nat) (l : list nat) (la : list term) (lr : list ((list nat) × term)) : list ((list nat) × term) :=
 match la with
 |[] => lr
 | h :: t => genIndex' (s + 1) l  t (lr ++ [((l ++ [s]), h)])
 end.

Definition genIndex (l : list nat) (la : list term) := genIndex' 0 l la [].   

Definition unfold_step (cstrs :list ((list nat) × term)) (ts : list ((list nat) × term)) (rem_ts : list ((list nat) × term))
                             : (((list ((list nat) × term)) × (list ((list nat) × term))) × (list ((list nat) × term))) := 
 match ts with
 | [] => (cstrs, rem_ts, nil)
 | (ls, ((tApp (tConstruct typeInfo cstrInd ls') args)))  :: t => ((cstrs ++ [(ls, tConstruct typeInfo cstrInd ls')], t, ((genIndex ls args) ++ rem_ts)))
 | (ls, (tRel k)) :: t => (cstrs, t, rem_ts)
 | (ls, (tApp (tInd indType ls') args)) :: t => (cstrs, t, ((genIndex ls args) ++ rem_ts)) 
 | (ls, (tInd indType ls')) :: t =>  (cstrs, t, rem_ts)
 | (ls, _) :: t => (cstrs, t, rem_ts) 
 end.   


(* Initialize with [], [([], bigTerm)], [] *)

Fixpoint unfold_step_iter (fuel : nat) 
                    (t : (((list ((list nat) × term)) × (list ((list nat) × term))) × (list ((list nat) × term)))) : 
                         (((list ((list nat) × term)) × (list ((list nat) × term))) × (list ((list nat) × term))) :=
  match fuel with
  | 0 => t
  | S m => unfold_step_iter m (unfold_step (fst (fst t)) (snd (fst t)) (snd t))
 end.
 
Definition unfoldCons (fuel : nat) (t : term) :=
 fst (fst (unfold_step_iter fuel ([], [([], t)], []))).
 
Definition unfoldConsRem (fuel : nat) (t : term) :=
 snd (fst (unfold_step_iter fuel ([], [([], t)], []))) ++ snd (unfold_step_iter fuel ([], [([], t)], [])) .   
                         
                         
 
Check length.*)

 

Check ([{|
            decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Coq"%bs], "eq"%bs);
                     inductive_ind := 0
                   |} [])
                [tInd {| inductive_mind := (MPfile ["Top"%bs], "myType"%bs); inductive_ind := 0 |} [];
                 tApp
                   (tConstruct
                      {| inductive_mind := (MPfile ["Top"%bs], "myType"%bs); inductive_ind := 0 |} 2 [])
                   [tRel 0; tRel 2]; tRel 1]
          |};
          {|
            decl_name := {| binder_name := nNamed "b"%bs; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd
                {|
                  inductive_mind :=
                    (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaCoq"%bs]) "String"%bs, "t"%bs);
                  inductive_ind := 0
                |} []
          |};
          {|
            decl_name := {| binder_name := nNamed "x"%bs; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd {| inductive_mind := (MPfile ["Top"%bs], "myType"%bs); inductive_ind := 0 |} []
          |};
          {|
            decl_name := {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tInd
                {|
                  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "nat"%bs);
                  inductive_ind := 0
                |} []
          |}]).   
              
          

  
