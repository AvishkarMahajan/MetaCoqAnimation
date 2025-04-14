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


Inductive myType : Set :=
| mycr2 : nat -> myType
| mycr4 : string -> nat -> myType
| mycr1 : string -> nat -> myType
| mycr3 : myType.



Inductive baz : nat -> myType -> string -> Prop :=
 | bazCon : forall (a : nat), forall (x : myType), forall (b : string), mycr1 b a = x -> baz a x b.  (*RHS of equality not v imp*)
 


MetaCoq Quote Recursively Definition bazTerm := baz.

Print bazTerm. 

(* Print program.
Print global_env.
Print global_decl. *)

Parameter error : kername × global_decl.


Parameter error2 : one_inductive_body.

Parameter error3 : constructor_body.

(* Print one_inductive_body. *)



Definition extractIndDecl (x : global_decl) : option mutual_inductive_body :=
 match x with
  | InductiveDecl y => Some y
  | _ => None
 end.
Compute (option_map ind_ctors (option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (tl (tl ((declarations (fst bazTerm))))))))))).

(* Compute (option_map cstr_type (option_map (hd error3) (option_map ind_ctors(option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst bazTerm)))))))))). *)

Compute (option_map cstr_args (option_map (hd error3) (option_map ind_ctors(option_map (hd error2) (option_map ind_bodies (extractIndDecl (snd (hd error (declarations (fst bazTerm)))))))))).
(* 1st and 3rd computations should have all info needed to build patternmatch fn *)

MetaCoq Quote Definition con3 := (fun x => match x with
                                                | mycr1 a b  =>  Some (a, b)
                                                | _ => None
                                               end).
Print con3.


(* Goal :

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
                  |} []];
             tApp
               (tConstruct
                  {|
                    inductive_mind := (MPfile ["Datatypes"%bs; "Init"%bs; "Coq"%bs], "prod"%bs);
                    inductive_ind := 0
                  |} 0 [])
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
                  |} []; tRel 1; tRel 0]]
      |};
      
      
 AND ANOTHER FUNCTION THAT GOES FROM
 
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



      
          
              
          

  
