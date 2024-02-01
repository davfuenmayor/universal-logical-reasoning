(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory base (* Technical configuration settings *)
imports HOL.Nitpick HOL.Sledgehammer "HOL-Eisbach.Eisbach"
begin

(********** Override Sledgehammer and Nitpick default params **************)
declare[[smt_timeout=30]]
(* declare[[show_types]] *)
declare[[syntax_ambiguity_warning=false]]
sledgehammer_params[isar_proof=false,abduce=0,falsify=false]
nitpick_params[assms=true, user_axioms=true, show_all, expect=genuine, format=3] (*default Nitpick settings*)


(*************** Hide notation/symbols from the library  *****************)

(*We only use a few things from the Isabelle library. We hide many symbols and notation to avoid collisions.*)
hide_const(open) Set.subset Set.subset_eq Set.supset Set.supset_eq 
                 Set.union Set.inter 
                 Set.range Set.image Set.vimage  
                 Set.is_empty Set.member Set.is_singleton
                 Relation.converse Relation.Range Relation.total 
                 Complete_Lattices.Inter Complete_Lattices.Union 
                 List.list.Nil List.list.map 
                 Hilbert_Choice.bijection Fun.comp Transitive_Closure.reflcl
                 Orderings.top_class.top Orderings.bot_class.bot
                 BNF_Def.convol 
                 Product_Type.prod Product_Type.Pair Product_Type.Pair_Rep
                 Fields.inverse_class.inverse_divide
                 Transitive_Closure.trancl Transitive_Closure.rtrancl

no_notation (*so we can use those symbols for our own purposes*)
  Set.subset  ("'(\<subset>')") and Set.subset  ("(_/ \<subset> _)" [51, 51] 50) and
  Set.subset_eq  ("'(\<subseteq>')") and Set.subset_eq  ("(_/ \<subseteq> _)" [51, 51] 50) and
  Set.supset  ("'(\<supset>')") and Set.supset  ("(_/ \<supset> _)" [51, 51] 50) and
  Set.supset_eq  ("'(\<supseteq>')") and Set.supset_eq  ("(_/ \<supseteq> _)" [51, 51] 50) and
  Set.union (infixl "\<union>" 65) and Set.inter (infixl "\<inter>" 70) and
  Set.member  ("'(:')") and Set.member  ("(_/ : _)" [51, 51] 50) and
  Complete_Lattices.Inter ("\<Inter>") and Complete_Lattices.Union ("\<Union>") and
  List.list.Nil ("[]") and
  Relation.converse ("(_\<inverse>)" [1000] 999) and
  Fun.comp (infixl "\<circ>" 55) and
  Transitive_Closure.reflcl ("(_\<^sup>=)" [1000] 999) and
  Orderings.top_class.top ("\<top>") and
  Orderings.bot_class.bot ("\<bottom>") and
  BNF_Def.convol ("\<langle>(_,/ _)\<rangle>") and
  Product_Type.Pair ("(_,/ _)" [21, 20] 20) and
  Fields.inverse_class.inverse_divide (infixl "'/" 70) and
  Transitive_Closure.trancl ("(_\<^sup>+)" [1000] 999) and Transitive_Closure.rtrancl ("(_\<^sup>*)" [1000] 999)
no_syntax
  "_Finset" :: "args \<Rightarrow> 'a set"    ("{(_)}")


(**********************  Alternative notations ***************************)

(*Introduce alias for type bool*)
type_synonym o = bool ("o")

(*We introduce (pedagogically convenient) alternative notation for HOL logical constants*)
notation HOL.All ("\<forall>") 
notation HOL.Ex  ("\<exists>")

notation HOL.True  ("\<top>")
notation HOL.False ("\<bottom>")

notation(input) HOL.Not ("'(\<not>')") (*so we can refer to negation as: (\<not>)*)

notation HOL.implies (infixr "\<rightarrow>" 25)
notation HOL.iff (infixr "\<leftrightarrow>" 25)

abbreviation (input) seilpmi  (infixl "\<leftarrow>" 25) (*for convenience*)
  where "A \<leftarrow> B \<equiv> B \<rightarrow> A"

(*Add (binder) notation for definite descriptions (incl. binder notation)*)
notation(input) HOL.The ("\<iota>")
notation(input) HOL.The (binder "\<iota>" 10)

(*Add (binder) notation for indefinite descriptions aka. Hilbert's epsilon or choice operator*)
notation(input) Hilbert_Choice.Eps ("\<epsilon>")
notation(input) Hilbert_Choice.Eps (binder "\<epsilon>" 10)

(*Sanity check*)
lemma "(\<iota> x. A x) = (THE x. A x)" ..
lemma "(\<epsilon> x. A x) = (SOME x. A x)" ..

end