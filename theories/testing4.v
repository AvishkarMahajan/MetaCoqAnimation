Require Import Animation.AnimationDispatch.
Require Import Animation.AnimationEngine.


Require Import Animation.EqualityResolution.

Require Import Animation.MetaRocqUtils.
Require Import Animation.PatternCompilation.

Require Import List.
Require Import MetaRocq.Template.All.
Import monad_utils.MRMonadNotation.
Unset MetaRocq Strict Unquote Universe Mode.


Import MetaRocqNotations.

Local Open Scope nat_scope.
Open Scope bs.
Print option.






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


Definition stack := list nat.
Definition prog := list sinstr.



Definition eqFnsinstr (t1 t2 : sinstr) : bool :=

  if decEqsinstr t1 t2 then true else false.  
    
(*
Inductive stack_step (st : state) : prog × stack → prog × stack → Prop :=
  | SS_Push : ∀ stk n p,
    stack_step st (SPush n :: p, stk) (p, n :: stk)
  | SS_Load : ∀ stk i p,
    stack_step st (SLoad i :: p, stk) (p, st i :: stk)
  | SS_P : ∀ stk n m p,
    stack_step st (SPlus :: p, n::m::stk) (p, (m+n)::stk)
  | SS_Minus : ∀ stk n m p,
    stack_step st (SMinus :: p, n::m::stk) (p, (m-n)::stk)
  | SS_Mult : ∀ stk n m p,
    stack_step st (SMult :: p, n::m::stk) (p, (m×n)::stk).
*)
Definition unwrap (A: Type) (x : ind_tp A) : A :=
match x with
| indWrap x' => x'
end.
Print ind_tp.
 
Inductive stack_step : (ind_tp state) -> list sinstr × list nat -> list sinstr × list nat -> Prop :=
   | SS_Push : forall  st stk n p ps0 ps1, ps0 = (SPush n :: p, stk) /\ ps1 = (p, n :: stk)  -> 
    stack_step st ps0 ps1 
   
    
   | SS_Load : forall  st stk i p ps0 ps1, ps0 = (SLoad i :: p, stk) /\ ps1 = (p, ((unwrap state st) i) :: stk) ->
    stack_step st ps0 ps1 
    
   | SS_P : forall st stk n m p ps0 ps1, ps0 = (SPlus :: p, n::m::stk) /\ ps1 = (p, (m+n)::stk) ->
    stack_step st ps0 ps1 
   | SS_Minus : forall st stk n m p ps0 ps1, ps0 = (SMinus :: p, n::m::stk) /\ ps1 = (p, (m-n)::stk) ->
    stack_step st ps0 ps1 
   | SS_Mult : forall st stk n m p ps0 ps1, ps0 = (SMult :: p, n::m::stk) /\ ps1 = (p, (m*n)::stk) ->
    stack_step st ps0 ps1 .
    
    
(*
Unset Universe Checking.
Definition animateInductive'' {A : Type} (ind : A) (kn : kername) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad (list term) :=
allClauseData <- get_data' kn modes ;;

let clLst := clause_lst allClauseData in


tms <- anim_all_cl_lst ind kn clLst modes fuel ;;
(*
let inductData := prod_in_out (get_fixpt_data allClauseData) in

let u := (mk_rec_fn (mk_all_ind_top (inductData) kn) 0)  in
          u' <- tmEval all u ;;
          t' <- tmEval all (typeConstrPatMatch.unwrap_option_term (DB.deBruijnOption u)) ;;
          tmPrint t' ;;
               f <- tmUnquote t';;
               tmPrint f ;;
              tmEval hnf (my_projT2 f) >>=
              tmDefinitionRed_ false (String.append (snd kn) "AnimatedTopFn") (Some hnf) ;; *) tmReturn tms.
(*              
MetaRocq Run (animateInductive'' stack_step <?stack_step?> [("stack_step",([0;1],[2]))] 200).
*)
MetaRocq Run (d <- get_data' <?stack_step?> [("stack_step",([0;1],[2]))];; cd' <- tmEval all (clause_lst d);; tmPrint cd').

Parameter fkTm : term.

Definition animate_one_conj_let_cl'' {A : Type} (ind : A) (kn : kername) (conjunct' : (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=
let  inputVarsLst := get_conj_input_var_lst conjunct' allVarTpInf (modes) (predTypeInf) in
animate_one_conj_any_let ind kn conjunct' inputVarsLst partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel.

Fixpoint animate_list_conj_let_cl'' {A : Type} (ind : A) (kn : kername) (conjs : list (term * (string * term))) (partialLetfn : term -> term) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (fuel : nat) : TemplateMonad (term -> term) :=

match conjs with
 | [] => tmReturn partialLetfn
 | h :: t => lFn' <- animate_one_conj_let_cl'' ind kn h partialLetfn (modes) (predTypeInf) (allVarTpInf) fuel ;; animate_list_conj_let_cl'' ind kn t lFn' (modes) (predTypeInf) (allVarTpInf) fuel
end.
Definition animate_list_let_and_pred_guard'' {A : Type} (ind : A) (kn : kername) (lConjs'' : list (term × (string × term))) (gConjsEq : list term) (gConjsPred'' : list (term × (string × term))) (inVars : list (prod string term)) (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=
lConjs <- tmEval all lConjs'';; 
gConjsPred <- tmEval all gConjsPred'';;
tmDefinition "ss_pushLC" lConjs ;; 
tmDefinition "ss_pushPTInf" predTypeInf;;
tmDefinition "ss_pushAllTInf" allVarTpInf ;;
tmDefinition "ss_pushModes" modes ;;


letBind <- animate_list_conj_let_cl''  (ind) kn  lConjs  (fun t : term => t) (modes) (predTypeInf) (allVarTpInf) (fuel) ;;
tmPrint letBind ;;


gFun <- animate_list_conj_guard_eq ind kn gConjsEq allVarTpInf outVars fuel ;;
let guardConEqAn := (tApp gFun [tVar "fuel"; mk_out_poly_prod_tm (allVarTpInf)]) in 
combineGuard <- animate_list_conj_pred_guard_br_out_bool (ind) (kn) (gConjsPred) (modes) (predTypeInf) (allVarTpInf) (outVars) (guardConEqAn) (fuel);;
tmPrint combineGuard ;;
tmReturn fkTm.
(*
match inVars with
 | h :: rest => tmReturn (mk_lam_tp (app (mk_animated_fn_nm lhsPreds) [("fuel", <%nat%>)]) (tLam "input" (tApp <%animation_result%> [telescope_to_prod_type inVars])(split_inputs' inVars (letBind combineGuard))))
 | [] => tmReturn (mk_lam_tp (app (mk_animated_fn_nm lhsPreds) [("fuel", <%nat%>)]) (split_inputs' inVars (letBind combineGuard)))
end. 
*)

Definition compileLetBindingsAndGuards'' {A : Type} (ind : A) (kn : kername) (bigConj : term) (cstrNm : string) (inVars : list (prod string term))  (outVars : list (prod string term)) (modes : list (string * ((list nat) * (list nat)))) (predTypeInf : list (string * (list term))) (allVarTpInf : list (string * term)) (lhsPreds : list (string * term)) (fuel : nat) : TemplateMonad term :=

let listAllConjs := get_list_conj_all bigConj in
let gConjsEq := filter_conjs_eq listAllConjs in
(*
lAC' <- tmEval all listAllConjs ;;
*)
(*tmPrint lAC';;*)

lConjs' <- (get_sorted_oriented_conjs_let modes listAllConjs [] [] [] (map fst inVars) fuel) ;;

let lConjs := remove_duplicate_defs (attach_output_var_to_sorted_conjs lConjs' allVarTpInf modes predTypeInf) (map fst inVars) in
(*
gConjs' <- (get_sorted_oriented_conjs_guard modes listAllConjs [] [] [] (map fst inVars) fuel) ;;
gConjs <- tmEval (all) gConjs' ;;
*)

let gConjsPred := filter_conjs_pred' (attach_output_var_to_sorted_conjs listAllConjs allVarTpInf modes predTypeInf)  in
gc'' <- tmEval all gConjsPred;;
lc'' <- tmEval all lConjs ;;
tmPrint gc'';;
tmPrint lc'';;

(*tmPrint lConjs;;
tmPrint gConjsEq;;*)

animate_list_let_and_pred_guard'' ind kn lConjs gConjsEq gConjsPred inVars outVars (modes) (predTypeInf) (allVarTpInf) (lhsPreds) fuel ;;
tmReturn fkTm.
(*
t'' <- tmEval all  (typeConstrPatMatch.unwrap_option_term (DB.deBruijnOption t)) ;;
*)
(*
tmPrint t'';;
*)
(*
f <- tmUnquote t'' ;;
tmEval hnf (my_projT2 f) >>=
    tmDefinitionRed_ false (String.append cstrNm "Animated") (Some hnf) ;;
*)
(*
tmReturn t.
*)
(*
tmReturn t''.
*)
Definition an_one_cl'' {A : Type} (ind : A) (kn : kername)  (oneClause : ((string * string) * term)) (modes : list (string * ((list nat) * (list nat)))) (fuel : nat) : TemplateMonad term :=
allClauseData <- get_data' kn modes ;;
mut <- tmQuoteInductive kn ;; 
let allTpData := (getClauseTpInfo (ind_bodies mut)) in
let cstrNm := snd (fst oneClause) in 

                       
let fixptData := prod_in_out (get_fixpt_data allClauseData) in
let conjlhs := conj_lhs oneClause in

let allVarTp := get_all_vars_tp_inf oneClause allTpData in
let inV := get_vars_tp (conj_in_vars oneClause modes) (allVarTp) in
let outV := get_vars_tp (conj_out_vars oneClause modes) (allVarTp) in
let predTps := all_ind_tp_data allClauseData in
let predTpsAn := animation_tp allClauseData in
let predTpsOccAn := get_pred_occ_an oneClause fixptData predTpsAn in
c <- tmEval all conjlhs ;;
c1 <- tmEval all inV ;;
c2 <- tmEval all outV ;;
c3 <- tmEval all predTps ;;
c4 <-tmEval all allVarTp ;;
c5 <- tmEval all predTpsOccAn ;;





(compileLetBindingsAndGuards'' ind kn c cstrNm c1 c2 modes c3 c4 c5 fuel). 




MetaRocq Run (an_one_cl'' stack_step <?stack_step?> ("stack_step", "SS_Push",
  tProd {| binder_name := nAnon; binder_relevance := Relevant |}
    (tApp <%and%>
       [tApp <%eq%>
          [tApp <%prod%>
             [tApp <%list%>
                [tInd
                   {|
                     inductive_mind := (MPfile ["testing4"; "Animation"], "sinstr"); inductive_ind := 0
                   |} []];
              tApp <%list%> [<%nat%>]];
           tVar "ps0";
           tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
             [tApp <%list%>
                [tInd
                   {|
                     inductive_mind := (MPfile ["testing4"; "Animation"], "sinstr"); inductive_ind := 0
                   |} []];
              tApp <%list%> [<%nat%>];
              tApp (tConstruct {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
                [tInd
                   {|
                     inductive_mind := (MPfile ["testing4"; "Animation"], "sinstr"); inductive_ind := 0
                   |} [];
                 tApp
                   (tConstruct
                      {|
                        inductive_mind := (MPfile ["testing4"; "Animation"], "sinstr");
                        inductive_ind := 0
                      |} 0 [])
                   [tVar "n"];
                 tVar "p"];
              tVar "stk"]];
        tApp <%eq%>
          [tApp <%prod%>
             [tApp <%list%>
                [tInd
                   {|
                     inductive_mind := (MPfile ["testing4"; "Animation"], "sinstr"); inductive_ind := 0
                   |} []];
              tApp <%list%> [<%nat%>]];
           tVar "ps1";
           tApp (tConstruct {| inductive_mind := <?prod?>; inductive_ind := 0 |} 0 [])
             [tApp <%list%>
                [tInd
                   {|
                     inductive_mind := (MPfile ["testing4"; "Animation"], "sinstr"); inductive_ind := 0
                   |} []];
              tApp <%list%> [<%nat%>]; tVar "p";
              tApp (tConstruct {| inductive_mind := <?list?>; inductive_ind := 0 |} 1 [])
                [<%nat%>; tVar "n"; tVar "stk"]]]])
    (tApp (tVar "stack_step") [tVar "st"; tVar "ps0"; tVar "ps1"])) [("stack_step",([0;1],[2]))] 200).
Check ss_pushLC.
Parameter fkTm2 : (term × string × term).  
Check nth.  
Compute (tl(tl (tl ss_pushLC))).
Definition ss_pushLC0 :=
nth 0 ss_pushLC fkTm2.



Definition ss_pushLC1 :=
nth 1 ss_pushLC fkTm2.

Definition ss_pushLC2 :=
nth 2 ss_pushLC fkTm2.

Definition ss_pushLC3 :=
nth 3 ss_pushLC fkTm2.
Compute ss_pushLC3.

    
MetaRocq Run (animate_one_conj_let_cl'' (stack_step) (<?stack_step?>) (ss_pushLC3) (fun t : term => t) ss_pushModes ss_pushPTInf ss_pushAllTInf 100).

MetaRocq Run (animate_list_conj_let_cl'' (stack_step) (<?stack_step?>) ([ss_pushLC0]) (fun t : term => t) ss_pushModes ss_pushPTInf ss_pushAllTInf 100).
(*
MetaRocq Run (animate_list_conj_let_cl'' (stack_step) (<?stack_step?>) (ss_pushLC) (fun t : term => t) ss_pushModes ss_pushPTInf ss_pushAllTInf 100).
*)
(* 5.51 *)
                   
Set Universe Checking.
*)
MetaRocq Run (animateInductive stack_step <?stack_step?> [("stack_step",([0;1],[2]))] 200).


