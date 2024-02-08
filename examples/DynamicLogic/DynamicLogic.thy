(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory DynamicLogic
  imports "../../library/endorels"
begin

section \<open>Shallow embedding\<close>

typedecl w (*type of worlds or states*)
type_synonym \<sigma> = "Set(w)" (*type of propositions or predicates*)
type_synonym \<pi> = "ERel(w)" (*type of actions or programs*)

(*We now introduce our program-indexed family of modalities via the following definitions:*)

(*P holds in *every* state reachable (from the currest state) by executing program/action 'a'*)
abbreviation(input) pBox::"\<pi>-Index(EOp(\<sigma>))" ("[_]_") (*type: ERel(w) \<Rightarrow> (Set(w) \<Rightarrow> Set(w))*)
  where "[a]P \<equiv> \<lambda>w. \<forall>v. a w v \<rightarrow> P v"
(*P holds in *at least one* state reachable (from the currest state) by executing program/action 'a'*)
abbreviation(input) pDia::"\<pi>-Index(EOp(\<sigma>))" ("<_>_") (*type: ERel(w) \<Rightarrow> (Set(w) \<Rightarrow> Set(w))*)
  where "<a>P \<equiv> \<lambda>w. \<exists>v. a w v \<and> P v"

(*Note that in fact*)
lemma pBox_char: "pBox = rDualPreimage" unfolding rDualPreimage_def by simp
lemma pDia_char: "pDia = rPreimage" unfolding rPreimage_def by simp

(*Diamond (resp. Box) is monotonic (resp. antimonotonic) wrt. relation ordering*)
lemma "a \<subseteq>\<^sup>r b \<longrightarrow> <a>P \<subseteq> <b>P" by (smt (verit, best) subset_def)
lemma "a \<subseteq>\<^sup>r b \<longrightarrow> [b]P \<subseteq> [a]P" by (simp add: subset_def)

(*For a shallow semantical embedding of a dynamic logic we add a layer of syntactic sugar *)
notation compl ("\<^bold>\<not>_"[55]56)
notation inter (infixr "\<^bold>\<and>" 54)
notation union (infixr "\<^bold>\<or>" 53)
notation univ  ("\<^bold>\<top>")
notation empty ("\<^bold>\<bottom>")


section \<open>Operations\<close>

(*We explore the (algebraic) operations on actions/programs. 
  For instance actions/programs can be combined via a sequential or choice execution.*)

(*Sequential execution 'a' followed by 'b'*)
abbreviation seq_composition::"\<pi> \<Rightarrow> \<pi> \<Rightarrow> \<pi>" (infixr ";" 75)
  where "a ; b \<equiv> b \<circ>\<^sup>r a"

lemma "[a;b]P = [a][b]P" unfolding rcomp_def by auto
lemma "<a;b>P = <a><b>P" unfolding rcomp_def by auto

(*Choice: execute a or b (non-deterministically)*)
abbreviation choice::"\<pi> \<Rightarrow> \<pi> \<Rightarrow> \<pi>" (infixr "+" 75)
  where "a + b \<equiv> a \<union>\<^sup>r b"

(*P holds in every state reachable via execution of the action/program 'a+b' if and only if P holds 
 in every state reachable via execution of 'a' *and* also in every state reachable via execution of 'b'*)
lemma "[a+b]P = ([a]P) \<^bold>\<and> ([b]P)" unfolding inter_def union_def by blast

(*P holds in at least one state reachable via execution of the action/program 'a+b' if and only if P holds 
 in at least one state reachable via execution of 'a' *or*  in at least one state reachable via execution of 'b'*)
lemma "<a+b>P = (<a>P) \<^bold>\<or> (<b>P)" unfolding inter_def union_def by blast

(*Non-deterministic choice for arbitrary sets: execute any action/program among those in S*)
abbreviation choiceS::"Set(\<pi>) \<Rightarrow> \<pi>" ("\<Sigma>")
  where "\<Sigma> S \<equiv> \<Union>\<^sup>rS" 

lemma "[\<Sigma> S]P = \<Inter>\<lbrakk>(\<lambda>x. [x]P) S\<rbrakk>" unfolding  biginter_def bigunionR_simpdef fImage_def by fastforce
lemma "<\<Sigma> S>P = \<Union>\<lbrakk>(\<lambda>x. <x>P) S\<rbrakk>" unfolding  bigunion_def bigunionR_simpdef fImage_def by fastforce

(*(Reflexive-)transitive closure: "repeat a an undetermined number of times"*)
definition tran_closure::"\<pi> \<Rightarrow> \<pi>" ("(_\<^sup>+)" 99)
  where "a\<^sup>+ \<equiv> \<Inter>\<^sup>r(\<lambda>R. transitive R \<and> a \<subseteq>\<^sup>r R)"
abbreviation refl_tran_closure::"\<pi> \<Rightarrow> \<pi>" ("(_\<^sup>* )" [1000] 999)
  where "a\<^sup>* \<equiv> a\<^sup>+ \<union>\<^sup>r (=)"

(*Some properties of the transitive and reflexive-transitive closure: *)
lemma "a\<^sup>+ = (a\<^sup>* ; a)" oops (*this holds but needs to be proven by hand*) 
lemma "q \<subseteq> p \<^bold>\<and> [a]q \<longrightarrow> q \<subseteq> [a\<^sup>*]p" oops (*this holds but needs to be proven by hand*) 

(*\<^bold>E\<^sup>GP stands for "Everyone in group G knows that P"*)
abbreviation Eknows ("\<^bold>E\<^sup>_") where "\<^bold>E\<^sup>G P \<equiv> [\<Sigma> G]P"
(*\<^bold>C\<^sup>GP stands for "It is common knowledge in group G that P"*)
abbreviation Cknows ("\<^bold>C\<^sup>_") where "\<^bold>C\<^sup>G P \<equiv> [(\<Sigma> G)\<^sup>+]P"

(*Exercise: encode the "muddy children" and "wise men" puzzle using the constructions above*)

end
