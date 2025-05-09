From Stdlib Require Import List.
Require Import List.

Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.

Require Import Animation.utils.
Require Import Animation.animationFullExProof.

Import MetaRocqNotations.

Require Import PeanoNat.
Local Open Scope nat_scope.

Inductive myType' : Set :=
| mycr1' : nat -> myType'
| mycr2' : nat -> myType'.

Inductive myType : Set :=
| mycr2 : myType' -> nat -> myType
| mycr3 : myType.




(* Print baz'Term. *) 

Definition extractIndDecl (x : global_decl) : option mutual_inductive_body :=
 match x with
  | InductiveDecl y => Some y
  | _ => None
 end.
 
Parameter error : kername × global_decl.


Parameter error2 : one_inductive_body.

Parameter error3 : constructor_body.

Parameter error4 : context_decl.
Parameter termErr : term.

Check rev.
Print context.






(* Print program.
Print global_env.
Print global_decl. *)



(* Print one_inductive_body. *)

(*Compute (tl (map extractIndDecl (map snd (declarations (fst baz'Term))))).*)

Definition extractTypeData (p : program) : list (option mutual_inductive_body) := 
 (map extractIndDecl ((map snd ((tl (tl (declarations (fst p)))))))).

(* Compute (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (tl (tl ((declarations (fst baz'Term))))))))))).*)

(* Compute (option_map cstr_type (option_map (hd error3) (option_map ind_ctors(option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst bazTerm)))))))))). *)
Definition extractPatMatData (p : program) : term :=
 let r := 
     (option_map decl_type (option_map (hd error4) (option_map cstr_args (option_map (hd error3) (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst p)))))))))))) in
     match r with
      | Some x => x
      | None => termErr
     end.    
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
 (*| (str, (tApp (tInd indType ls') args)) :: t => (i + (length args), t, ((str, (tInd indType ls'), (map fst (genVarlst i args))) :: resolvedTs), (app (genVarlst i args) remTs)) *)
 | (str, (tConstruct typeInfo k [])) :: t => (i, t, (((str, (tConstruct typeInfo k []), nil)) :: resolvedTs), remTs)
            
 | (str, (tApp func args)) :: t => (i + (length args), t, ((str, func, (map fst (genVarlst i args))) :: resolvedTs), (app (genVarlst i args) remTs))
(* | (str, (tInd indType ls')) :: t => (i, t, (((str, (tInd indType ls'), nil)) :: resolvedTs), remTs) *)
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
 rev (snd (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], [])))).
 
Compute (preProcCons 20 (tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Corelib"%bs], "eq"%bs);
                     inductive_ind := 0
                   |} [])
                [tInd
                   {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType"%bs); inductive_ind := 0 |}
                   [];
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["typeConNest2"%bs], "myType"%bs); inductive_ind := 0
                      |} 0 [])
                   [tApp
                      (tConstruct
                         {|
                           inductive_mind := (MPfile ["typeConNest2"%bs], "myType'"%bs);
                           inductive_ind := 0
                         |} 0 []) [tRel 2]; tRel 1]; tRel 0])). 


Compute ((preProcCons 20 (
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
                         |} 0 []) [tVar "a"%bs]; tVar "b"%bs]))). 
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




 



Definition preProcConsRem (fuel : nat) (t : term) : bool :=
 let r := app (snd ((unfoldConsStepIter fuel (0, [("x"%bs, t)], [], [])))) (snd (fst (fst (unfoldConsStepIter fuel (0, [("x"%bs, t)], [], []))))) in
  match r with
  | [] => true
  | _ => false
  end.
   
     
 
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


(* Print bazTerm. *)







(* MetaRocq Quote Definition con3 := (fun x => match x with
                                                | mycr2 a b  =>  Some true
                                                | _ => None
                                               end).
Print con3.

MetaRocq Quote Definition con4 := (fun x => match x with
                                                | mycr2 a b  =>  match a with
                                                                  | mycr1' m => Some true
                                                                  | _        => None
                                                                 end 
                                                | _ => None
                                               end).
                                               
Print con4.


MetaRocq Quote Definition con5 := (fun x => match x with
                                                | mycr2 a b  =>  match b with
                                                                  | S m => match a with
                                                                            | mycr1' j => Some true
                                                                            | _ => None
                                                                           end 
                                                                  
                                                                  | _        => None
                                                                 end 
                                                                 
                                                | _ => None
                                               end).
Print con5. *)


      
 


Fixpoint genBinderNameList (n : nat) : list (binder_annot name) :=
 match n with 
  | 0 => []
  | S m => {| binder_name := nNamed (String.append "n" (string_of_nat (S m))) ; binder_relevance := Relevant |} :: genBinderNameList m
 end. 

Fixpoint genBinNmLsStr (ls : list string) : list (binder_annot name) :=
 match ls with
  | [] => []
  | h :: t => {| binder_name := nNamed h ; binder_relevance := Relevant |} :: genBinNmLsStr t
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
      
      
      
      
      
      

          
 (*Definition mkPMBranch (cxt : list context_decl) (someVal : term) : option (branch term) :=
  match cxt with 
   | [] => None
   | (h :: t) => let d := decl_type h in 
                   match d with
                    | tApp
                       (tInd {|
                        inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Corelib"%bs], "eq"%bs);
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
                        inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Corelib"%bs], "eq"%bs);
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
   end. *)
   

Definition getcsAr (o : one_inductive_body) : string × list nat :=
 (ind_name o, (map cstr_arity (ind_ctors o))).
                 
Fixpoint extractTypeCsArlst (muts : list mutual_inductive_body) : list (string × list nat) :=
  match muts with
   | [] => []
   | (h :: t) => map getcsAr (ind_bodies h) ++ extractTypeCsArlst t
  end.  
   
   
   
Parameter error_nat : nat.
Parameter errorInd : inductive.
Parameter errorStr : string.
Parameter errorlstNat : list nat.


      
Definition getCstrIndex (s : (string × term) × list string) : nat := (* Get index of typeCon *)
  match s with
   | (str,
         tConstruct typeInfo
           k ls, lsStr)     => k
           
   | _ => error_nat        
  end. 

Definition getType (s : (string × term) × list string) :=  (*Get type of scrutinee var*)
  match s with
   | (str,
         tConstruct typeInfo
           k ls, lsStr)  => typeInfo
   | _ => errorInd
  end.         



Definition getTypeNm (s : (string × term) × list string) : string := (* Get name of type *)
 match s with 
  | (str,
         tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
           k ls, lsStr)     => nmStr
  | _ => errorStr
 end.           

Fixpoint chkMemberStr (s : string) (lStr : list string) : bool :=
 match lStr with
  | [] => false
  | (h :: t) => if (String.eqb s h) then true else chkMemberStr s t
 end.   

Fixpoint filterTypeCon (ls : list ((string × term) × list string)) (mut : list mutual_inductive_body) : 
                         list ((string × term) × list string) := (* Delete terms not corresponding to a valid typeCon *)
   match ls with
    | [] => []
    | h :: t => match h with 
                 | (str,
                    tConstruct {| inductive_mind := (loc, nmStr); inductive_ind := j |}
                    k ls, lsStr) => if (chkMemberStr nmStr (map fst (extractTypeCsArlst mut))) then h :: (filterTypeCon t mut) else (filterTypeCon t mut) 
                 | _ => (filterTypeCon t mut) 
                end        
   end.










Fixpoint getCstrArityLst' (typeName : string) (r : list (string × list nat)) : list nat := (* use String.eqb *)
 
  match r with
   | [] => errorlstNat
   | (h :: t) => if String.eqb typeName (fst h) then snd h else getCstrArityLst' typeName t
  end. 
  
Definition getCstrArityLst (typeName : string) (muts : list mutual_inductive_body) : list nat :=
 getCstrArityLst' typeName (extractTypeCsArlst muts).
   

Definition mkNoneBranch (n : nat) : branch term := mkNoneBr n (tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                        inductive_ind := 0
                      |} 1 [])
                   [tInd
                      {|
                        inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                        inductive_ind := 0
                      |} []]). (* Takes a arity and produces a branch term where return value is none *)

Definition mkSomeBranch (l : list string) (t : term) : branch term := 
  {|
    bcontext :=
    genBinNmLsStr l;
    bbody :=
    t
      |}.
            (* Takes a list of binder names and a return val and produces
a branch term *) 

Fixpoint untilLst (n : nat) (l : list nat) : list nat :=
 match n with
  | 0 => []
  | S m => match l with
            | [] => []
            | h :: t => (h :: untilLst m t)
           end
 
 end.         (* Return l upto the index before n *)

Fixpoint restLst (n : nat) (l : list nat) : list nat :=
 match n with 
  | 0 => tl l
  | S m => match l with
            | [] => []
            | h :: t => restLst m t
           end  (* Return l from the index after n *)
 end.

Definition mkBrLst (s : (string × term) × list string) (l : list mutual_inductive_body) (t : term) : list (branch term) :=
 let csArlst := (getCstrArityLst (getTypeNm s) l) in
  let index := getCstrIndex s in
  map mkNoneBranch (untilLst index csArlst) ++ [mkSomeBranch (rev (snd s)) t] ++ map mkNoneBranch (restLst index csArlst).  
   
  
      
Definition mkCase'  (s : (string × term) × list string) (l : list mutual_inductive_body) (t : term)  
                      : term :=
  
  (tCase
     {|
       ci_ind := getType s ;
       ci_npar := 0;
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := [];
       pcontext := [{| binder_name := nNamed (fst (fst s)); binder_relevance := Relevant |}];
       preturn :=
         (tApp
           (tInd
              {|
                inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                inductive_ind := 0
              |} [])
           [tInd
              {|
                inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                inductive_ind := 0
              |} []])
     |} (tVar (fst (fst s))) (* Should get changed to a tRel after deBruijning *)                                                                                                        
      (mkBrLst s l t)). 



MetaRocq Quote Definition idTerm := (fun x => x).
MetaRocq Quote Definition oBoolT := (Some true).
      
Definition identityTerm : term := idTerm. (* term rep of id function*)

Definition optBoolTrue : term := oBoolT. (* term rep of some true *)



      


Fixpoint mkPmNested' (ls : list ((string × term) × list string)) (mut : list mutual_inductive_body) : term :=
 match ls with
  | [] => identityTerm
  | (h :: nil) => mkCase' h mut optBoolTrue  
  | (h :: t) => mkCase' h mut (mkPmNested' t mut)
 end. 
 
Definition mkPmNested (ls : list ((string × term) × list string)) (mut : list mutual_inductive_body) : term :=
   mkPmNested' (filterTypeCon ls mut) mut.

Fixpoint removeOpt {A : Type} (optls : list (option A)) : list A :=
 match optls with
  | [] => []
  | (Some x :: t) => (x :: removeOpt t)
  | (None :: t) => removeOpt t
 end. 

Definition mkLam' (ls : list ((string × term) × list string)) (mut : list mutual_inductive_body) : option term :=
 match ls with 
 | [] => None
 | ((str,
         tConstruct typeInfo
           k js, strs) :: t'') => Some (tLambda {| binder_name := nNamed str; binder_relevance := Relevant |}
                                 (tInd typeInfo js) (mkPmNested ls mut))
 | _ => None                                
 end.
 
Definition mkLam (ls : list ((string × term) × list string)) (mut : list (option mutual_inductive_body)) : option term :=
  mkLam' (filterTypeCon ls (removeOpt mut)) (removeOpt mut).    
 
(*test inputs :*)


(* Definition testInput1 : list ((string × term) × list string) := [("x"%bs,
         tInd
           {|
             inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Corelib"%bs], "eq"%bs); inductive_ind := 0
           |} [], ["v1"%bs; "v2"%bs; "v3"%bs]);
        ("v2"%bs,
         tConstruct
           {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType"%bs); inductive_ind := 0 |} 0 [],
         ["v4"%bs; "v5"%bs]); ("v3"%bs, tRel 0, []);
        ("v4"%bs,
         tConstruct
           {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType'"%bs); inductive_ind := 0 |} 0 [],
         ["v6"%bs]); ("v5"%bs, tRel 1, []); ("v6"%bs, tRel 2, [])].
         
Definition testInput2 : list (option mutual_inductive_body) :=        
   [Some
          {|
            ind_finite := Finite;
            ind_npars := 0;
            ind_params := [];
            ind_bodies :=
              [{|
                 ind_name := "myType"%bs;
                 ind_indices := [];
                 ind_sort :=
                   sType
                     {|
                       t_set :=
                         {|
                           LevelExprSet.this := [(Level.lzero, 0)];
                           LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                         |};
                       t_ne := eq_refl
                     |};
                 ind_type :=
                   tSort
                     (sType
                        {|
                          t_set :=
                            {|
                              LevelExprSet.this := [(Level.lzero, 0)];
                              LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                            |};
                          t_ne := eq_refl
                        |});
                 ind_kelim := IntoAny;
                 ind_ctors :=
                   [{|
                      cstr_name := "mycr2"%bs;
                      cstr_args :=
                        [{|
                           decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                           decl_body := None;
                           decl_type :=
                             tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                                 inductive_ind := 0
                               |} []
                         |};
                         {|
                           decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                           decl_body := None;
                           decl_type :=
                             tInd
                               {|
                                 inductive_mind := (MPfile ["typeConNest2"%bs], "myType'"%bs);
                                 inductive_ind := 0
                               |} []
                         |}];
                      cstr_indices := [];
                      cstr_type :=
                        tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                          (tInd
                             {|
                               inductive_mind := (MPfile ["typeConNest2"%bs], "myType'"%bs);
                               inductive_ind := 0
                             |} [])
                          (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                             (tInd
                                {|
                                  inductive_mind :=
                                    (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                                  inductive_ind := 0
                                |} []) (tRel 2));
                      cstr_arity := 2
                    |};
                    {|
                      cstr_name := "mycr3"%bs;
                      cstr_args := [];
                      cstr_indices := [];
                      cstr_type := tRel 0;
                      cstr_arity := 0
                    |}];
                 ind_projs := [];
                 ind_relevance := Relevant
               |}];
            ind_universes := Monomorphic_ctx;
            ind_variance := None
          |};
        Some
          {|
            ind_finite := Finite;
            ind_npars := 0;
            ind_params := [];
            ind_bodies :=
              [{|
                 ind_name := "myType'"%bs;
                 ind_indices := [];
                 ind_sort :=
                   sType
                     {|
                       t_set :=
                         {|
                           LevelExprSet.this := [(Level.lzero, 0)];
                           LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                         |};
                       t_ne := eq_refl
                     |};
                 ind_type :=
                   tSort
                     (sType
                        {|
                          t_set :=
                            {|
                              LevelExprSet.this := [(Level.lzero, 0)];
                              LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                            |};
                          t_ne := eq_refl
                        |});
                 ind_kelim := IntoAny;
                 ind_ctors :=
                   [{|
                      cstr_name := "mycr1'"%bs;
                      cstr_args :=
                        [{|
                           decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                           decl_body := None;
                           decl_type :=
                             tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                                 inductive_ind := 0
                               |} []
                         |}];
                      cstr_indices := [];
                      cstr_type :=
                        tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                          (tInd
                             {|
                               inductive_mind :=
                                 (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                               inductive_ind := 0
                             |} []) (tRel 1);
                      cstr_arity := 1
                    |};
                    {|
                      cstr_name := "mycr2'"%bs;
                      cstr_args :=
                        [{|
                           decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                           decl_body := None;
                           decl_type :=
                             tInd
                               {|
                                 inductive_mind :=
                                   (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                                 inductive_ind := 0
                               |} []
                         |}];
                      cstr_indices := [];
                      cstr_type :=
                        tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                          (tInd
                             {|
                               inductive_mind :=
                                 (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                               inductive_ind := 0
                             |} []) (tRel 1);
                      cstr_arity := 1
                    |}];
                 ind_projs := [];
                 ind_relevance := Relevant
               |}];
            ind_universes := Monomorphic_ctx;
            ind_variance := None
          |};
        Some
          {|
            ind_finite := Finite;
            ind_npars := 0;
            ind_params := [];
            ind_bodies :=
              [{|
                 ind_name := "nat"%bs;
                 ind_indices := [];
                 ind_sort :=
                   sType
                     {|
                       t_set :=
                         {|
                           LevelExprSet.this := [(Level.lzero, 0)];
                           LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                         |};
                       t_ne := eq_refl
                     |};
                 ind_type :=
                   tSort
                     (sType
                        {|
                          t_set :=
                            {|
                              LevelExprSet.this := [(Level.lzero, 0)];
                              LevelExprSet.is_ok := LevelExprSet.Raw.singleton_ok (Level.lzero, 0)
                            |};
                          t_ne := eq_refl
                        |});
                 ind_kelim := IntoAny;
                 ind_ctors :=
                   [{|
                      cstr_name := "O"%bs;
                      cstr_args := [];
                      cstr_indices := [];
                      cstr_type := tRel 0;
                      cstr_arity := 0
                    |};
                    {|
                      cstr_name := "S"%bs;
                      cstr_args :=
                        [{|
                           decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
                           decl_body := None;
                           decl_type := tRel 0
                         |}];
                      cstr_indices := [];
                      cstr_type :=
                        tProd {| binder_name := nAnon; binder_relevance := Relevant |} (tRel 0) (tRel 1);
                      cstr_arity := 1
                    |}];
                 ind_projs := [];
                 ind_relevance := Relevant
               |}];
            ind_universes := Monomorphic_ctx;
            ind_variance := None
          |}].
         
Compute (mkLam testInput1 testInput2). 


Definition extractTypeData (p : program) : list (option mutual_inductive_body) := 
 (map extractIndDecl ((map snd ((tl (tl (declarations (fst p)))))))).

(* Compute (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (tl (tl ((declarations (fst baz'Term))))))))))).*)

(* Compute (option_map cstr_type (option_map (hd error3) (option_map ind_ctors(option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst bazTerm)))))))))). *)
Definition extractPatMatData

preProcConsRem fuel term *)

Definition mkLamfromInd (p : program) (fuel : nat) : option term :=
 let td := extractTypeData p in
  let pmd := extractPatMatData p in
   if (preProcConsRem fuel pmd) then (mkLam (preProcCons fuel pmd) td) else None. 
   
(* Compute (mkLamfromInd baz'Term 20).*)

Parameter errTm : term.

Definition removeopTm (o : option term) : term :=
 match o with
  | Some t => t
  | None => errTm
 end.  
 
 
Inductive myListType :Set :=
 | myListNil : myListType
 | myListCons : nat -> myListType -> myListType.
 
Inductive triple' : nat -> myListType -> Prop :=
 | triple'Con : forall (a : nat), forall (y : myListType), (myListCons a myListNil)  = y -> triple' a  y.  (*RHS of equality not v imp*)
 


MetaRocq Quote Recursively Definition triple'Term := triple'.

(* Compute ((extractPatMatData triple'Term)). *)

(* Compute (preProcCons 10 (extractPatMatData triple'Term)). *)

(* Compute (mkLamfromInd triple'Term 30). *)
MetaRocq Run (t <- DB.deBruijn (removeopTm (mkLamfromInd triple'Term 15));; tmEval all t >>= tmUnquote >>= tmPrint).
 
 
Inductive baz' : nat -> nat -> myType -> Prop :=
 | bazCon' : forall (a : nat), forall (x : nat), forall (y : myType), mycr2 (mycr1' a) (S x) = y -> baz' a x y.  (*RHS of equality not v imp*)
 

MetaRocq Quote Recursively Definition baz'Term := baz'. 

MetaRocq Run (t <- DB.deBruijn (removeopTm (mkLamfromInd baz'Term 20));; tmEval all t >>= tmUnquote >>= tmPrint).
  
(* Print tmQuote. *)

Inductive myProdType :Set :=
 | myProdCr' : nat -> nat -> myProdType.
 
Inductive tuple' : nat -> nat -> myProdType -> Prop :=
 | tuple'Con' : forall (a : nat), forall (b : nat), forall (y : myProdType), myProdCr' (S a) b = y -> tuple' a b y.  (*RHS of equality not v imp*)
 


MetaRocq Quote Recursively Definition tuple'Term := tuple'.
MetaRocq Run (t <- DB.deBruijn (removeopTm (mkLamfromInd tuple'Term 30));; tmEval all t >>= tmUnquote >>= tmPrint).



(* DOESN'T WORK FOR INSTANCES OF POLYMORPHIC TYPES

Inductive tuple : nat -> nat -> (prod nat nat) -> Prop :=
 | tupleCon : forall (a : nat), forall (b : nat), forall (y : (prod nat nat)), (a, b) = y -> tuple a b y.  (*RHS of equality not v imp*)
 
Check (prod nat nat).

MetaRocq Quote Recursively Definition tupleTerm := tuple.
Compute (preProcCons 25 (extractPatMatData tupleTerm)).

Compute (removeopTm (mkLamfromInd tupleTerm 25)).

MetaRocq Quote Definition prodFnTm := (fun v2 : (nat × nat) => match v2 with
                                                                | (a, b) => Some true
                                                                
                                                               end ).

Print prodFnTm. 




Inductive list3 : nat -> nat -> nat -> list nat -> Prop :=
 | list3Con : forall (a b c : nat), forall (y : list nat), [S a; b; c] = y -> list3 a b c y.  (*RHS of equality not v imp*)
 

MetaRocq Quote Recursively Definition list3Term := list3.

Compute (removeopTm (mkLamfromInd list3Term 25)).

(* Non-terminating Computation? *)

MetaRocq Run (t <- DB.deBruijn (removeopTm (mkLamfromInd list3Term 25));; tmEval all t (*>>= tmUnquote*) >>= tmPrint).*)
 

 
(* JUNK
Definition mkCase'' (s : (string × term) × list string) (retVal : term) (typeInfo : list (mutual_inductive_body))
      (finalValType : term) (*for now always option bool *)  : term := ...
 
 makeCase' s retVal = mkCase'' s retVal fixedParams...      
 
 
 Take typeCon and retVal and some fixed params and produce a tCase where branch corresponding to typeCon returns retVal and everything else returns 
None (bool) The error cases should just return retVal *) 
                
                
                
(* Check ({| inductive_mind := (MPfile ["typeCon"%bs], "myType"%bs); inductive_ind := 0 |}). *) 

(* Definition getPMIndex (cxt : list context_decl)  : option (nat) :=
  match cxt with 
   | [] => None
   | (h :: t) => let d := decl_type h in 
                   match d with
                    | tApp
                       (tInd {|
                        inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Corelib"%bs], "eq"%bs);
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
     |} (tVar scrutineeVar%bs) (*Should get changed to a tRel after deBruijning *)                                                                                                        
      brs). (*scrutineeType and scrutineeType' should be same *)  *)                  
                    
                    
(*Definition mkCase (scrutineeType' : inductive) (retOpType : term)
                     (scrutineeVar : string) (brs : list (branch term)) : term :=
  
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
     |} (tVar scrutineeVar%bs) (* Should get changed to a tRel after deBruijning *)                                                                                                        
      brs). (*scrutineeType and scrutineeType' should be same *) *) 
  
                    
                    
                    
                    
                    
       
     
      
      



      
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
                       inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
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
                         (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaRocq"%bs]) "String"%bs, "t"%bs);
                       inductive_ind := 0
                     |} []
               |}];
            cstr_indices := [];
            cstr_type :=
              tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                (tInd
                   {|
                     inductive_mind :=
                       (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaRocq"%bs]) "String"%bs, "t"%bs);
                     inductive_ind := 0
                   |} [])
                (tProd {| binder_name := nAnon; binder_relevance := Relevant |}
                   (tInd
                      {|
                        inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
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
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                 inductive_ind := 0
               |} 1 [])
            [tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "prod"%bs);
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind :=
                      (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaRocq"%bs]) "String"%bs, "t"%bs);
                    inductive_ind := 0
                  |} [];
                tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
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
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                 inductive_ind := 0
               |} 1 [])
            [tApp
               (tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "prod"%bs);
                    inductive_ind := 0
                  |} [])
               [tInd
                  {|
                    inductive_mind :=
                      (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaRocq"%bs]) "String"%bs, "t"%bs);
                    inductive_ind := 0
                  |} [];
                tInd
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
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

 

(* Check ([{|
            decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Corelib"%bs], "eq"%bs);
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
                    (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaRocq"%bs]) "String"%bs, "t"%bs);
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
                  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                  inductive_ind := 0
                |} []
          |}]). *)  
          
          
(*MetaRocq Unquote Definition fn5' := (tLambda {| binder_name := nNamed "x"%bs; binder_relevance := Relevant |}
  (tInd {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType"%bs); inductive_ind := 0 |} [])
  (tCase
     {|
       ci_ind := {| inductive_mind := (MPfile ["typeConNest2"%bs], "myType"%bs); inductive_ind := 0 |};
       ci_npar := 0;
       ci_relevance := Relevant
     |}
     {|
       puinst := [];
       pparams := [];
       pcontext := [{| binder_name := nNamed "x"%bs; binder_relevance := Relevant |}];
       preturn :=
         tApp
           (tInd
              {|
                inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                inductive_ind := 0
              |} [])
           [tInd
              {|
                inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                inductive_ind := 0
              |} []]
     |} (tVar "x"%bs)
     [{|
        bcontext :=
          [{| binder_name := nNamed "b"%bs; binder_relevance := Relevant |};
           {| binder_name := nNamed "a"%bs; binder_relevance := Relevant |}];
        bbody :=
          tCase
            {|
              ci_ind :=
                {|
                  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
                  inductive_ind := 0
                |};
              ci_npar := 0;
              ci_relevance := Relevant
            |}
            {|
              puinst := [];
              pparams := [];
              pcontext := [{| binder_name := nNamed "b"%bs; binder_relevance := Relevant |}];
              preturn :=
                tApp
                  (tInd
                     {|
                       inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                       inductive_ind := 0
                     |} [])
                  [tInd
                     {|
                       inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                       inductive_ind := 0
                     |} []]
            |} (tVar "b"%bs)
            [{|
               bcontext := [];
               bbody :=
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                        inductive_ind := 0
                      |} 1 [])
                   [tInd
                      {|
                        inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                        inductive_ind := 0
                      |} []]
             |};
             {|
               bcontext := [{| binder_name := nNamed "m"%bs; binder_relevance := Relevant |}];
               bbody :=
                 tCase
                   {|
                     ci_ind :=
                       {|
                         inductive_mind := (MPfile ["typeConNest2"%bs], "myType'"%bs);
                         inductive_ind := 0
                       |};
                     ci_npar := 0;
                     ci_relevance := Relevant
                   |}
                   {|
                     puinst := [];
                     pparams := [];
                     pcontext := [{| binder_name := nNamed "a"%bs; binder_relevance := Relevant |}];
                     preturn :=
                       tApp
                         (tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                              inductive_ind := 0
                            |} [])
                         [tInd
                            {|
                              inductive_mind :=
                                (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                              inductive_ind := 0
                            |} []]
                   |} (tVar "a"%bs)
                   [{|
                      bcontext := [{| binder_name := nNamed "j"%bs; binder_relevance := Relevant |}];
                      bbody :=
                        tApp
                          (tConstruct
                             {|
                               inductive_mind :=
                                 (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                               inductive_ind := 0
                             |} 0 [])
                          [tInd
                             {|
                               inductive_mind :=
                                 (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                               inductive_ind := 0
                             |} [];
                           tConstruct
                             {|
                               inductive_mind :=
                                 (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                               inductive_ind := 0
                             |} 0 []]
                    |};
                    {|
                      bcontext := [{| binder_name := nNamed "n"%bs; binder_relevance := Relevant |}];
                      bbody :=
                        tApp
                          (tConstruct
                             {|
                               inductive_mind :=
                                 (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                               inductive_ind := 0
                             |} 1 [])
                          [tInd
                             {|
                               inductive_mind :=
                                 (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                               inductive_ind := 0
                             |} []]
                    |}]
             |}]
      |};
      {|
        bcontext := [];
        bbody :=
          tApp
            (tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                 inductive_ind := 0
               |} 1 [])
            [tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                 inductive_ind := 0
               |} []]
      |}])). *)




(* Goal  (build pattern match branch) :

build function that goes from 

[{|
            decl_name := {| binder_name := nAnon; binder_relevance := Relevant |};
            decl_body := None;
            decl_type :=
              tApp
                (tInd
                   {|
                     inductive_mind := (MPfile ["Logic"%bs; "Init"%bs; "Corelib"%bs], "eq"%bs);
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
                    (MPdot (MPfile ["bytestring"%bs; "Utils"%bs; "MetaRocq"%bs]) "String"%bs, "t"%bs);
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
                  inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "nat"%bs);
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
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "option"%bs);
                 inductive_ind := 0
               |} 0 [])
            [tInd
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                 inductive_ind := 0
               |} [];
             tConstruct
               {|
                 inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Corelib"%bs], "bool"%bs);
                 inductive_ind := 0
               |} 0 []]
      |} 
 *)
