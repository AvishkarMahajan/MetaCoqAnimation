(* 

Proving a universally quantified statement about the soundness  of animation 

Consider an inductive relation I parameterized by component 

t : nat -> nat

(eg. I(t) a b holds iff b = t a)

Consider animate : term -> term 

Let t_uninterp be the uninterpreted function of type : nat -> nat

Suppose that forall t : nat -> nat 

quote t = tConst "t"

and that

unquote (tConst "t") = t

Given the following lemmas and axioms 

Lemma 2 (to be proven inside Coq):
forall s : String, 
  animate ((quote(I (t_uninterp))) [s / tConst “t_uninterp”]) = (animate ((quote(I (t_uninterp))))) [s / tConst “t_uninterp”] 

Lemma 3 (to be proven inside Coq) 

forall t : nat -> nat,

I (t) (inputVars, outputVars) <-> 
  (unquote (animate (quote (I(t_uninterp))))) [t/ t_uninterp]  (inputVars) = outputVars

Axiom 1 (must be assumed, cannot be proven inside Coq)

Forall Coq objects e1 : T1 -> T2, e2 : T1, 

quote(e1 e2) = quote(e1 e2_uninterp) [quote (e2)/quote(e2_uninterp)] 

where e2_uninterp is the uninterpreted object of type T1

Axiom 2 (must be assumed, cannot be proven inside Coq)

Forall f : term -> term, given an uninterpreted object a : T, 
If unquote (f (quote a)) exists then, 
Forall a’ : T, unquote (f (quote a) [quote a’ / quote a]) = (unquote (f (quote a))) [a’ / a] 









The goal is to prove that : 

forall t : nat -> nat : 
I (t) (inputVars, outputVars) <-> 
(unquote (animate (quote (I(t)))))  (inputVars) = outputVars

Pf
quote (I (t)) = quote(I (t_uninterp)) [tConst “t” / tConst “t_uninterp”] (Axiom 1)

animate ((quote(I (t_uninterp))) [tConst “t” / tConst “t_uninterp”]) = (animate ((quote(I (t_uninterp))))) [tConst “t” / tConst “t_uninterp”] (Lemma 2)

Therefore 

animate (quote (I(t))) = (animate ((quote(I (t_uninterp))))) [tConst “t” / tConst “t_uninterp”]


Lemma 3 : 

forall t : nat -> nat,

I (t) (inputVars, outputVars) <-> 
  (unquote (animate (quote (I(t_uninterp))))) [t/ t_uninterp]  (inputVars) = outputVars

Therefore we are required to prove that :
  (unquote (animate (quote (I(t_uninterp))))) [t/ t_uninterp] = unquote (animate ((quote(I (t_uninterp)))) [tConst “t” / tConst “t_uninterp”])


Let h : term -> term be such that, forall t : nat -> nat,  h (tConst "t") = animate (quote (I (t)))  

Then we are required to prove :

unquote (h (tConst "t_uninterp")) [t/t_uninterp] = unquote (h (tConst "t_uninterp") [tConst "t" / tConst “t_uninterp”])

This holds via Axiom 2.

Comments :

Maybe in the axioms = should be replaced by a weaker notion of equivalence? (i.e. two terms are equivalent if they are equal 
upto replacement of strings corresponding to bound vars in the object level etc.) 
Does that affect the proof?

 
Also a special case of the axioms is probably enough to make the proof go through.
*)



 

 
