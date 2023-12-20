(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory ModalLogic_shallow (* A shallow embedding of modal logic(s) *)
  imports ModalAlgebra
begin

(*A shallow semantical embedding of a (modal) logic consists in adding a layer of syntactic sugar 
  over the corresponding semantical structures (modal algebras) *)
notation compl ("\<^bold>\<not>_"[55]56)
notation inter (infixr "\<^bold>\<and>" 54)
notation union (infixr "\<^bold>\<or>" 53)
notation univ  ("\<^bold>\<top>")
notation empty ("\<^bold>\<bottom>")
notation iBox ("\<^bold>\<box>\<^sup>_") (*we can index modalities with objects of any type (e.g. numbers)*)
notation iDia ("\<^bold>\<diamond>\<^sup>_")

(*For example:*)
lemma "(A \<^bold>\<and> \<^bold>\<not>\<^bold>\<box>\<^sup>i(B)) = (A \<inter> \<midarrow>([i]B))" ..
lemma "(\<^bold>\<not>A \<^bold>\<or> \<^bold>\<diamond>\<^sup>i\<^bold>\<top> \<^bold>\<and> \<^bold>\<box>\<^sup>i\<^bold>\<bottom>) = (\<midarrow>A \<union> (<i> \<UU>) \<inter> [i]\<emptyset>)" ..

(*We can also add convenient abbreviations*)
abbreviation impl (infixr "\<^bold>\<rightarrow>" 51) 
  where "A \<^bold>\<rightarrow> B \<equiv> \<^bold>\<not>A \<^bold>\<or> B"
abbreviation dimpl (infixr "\<^bold>\<leftrightarrow>" 51) 
  where "A \<^bold>\<leftrightarrow> B \<equiv> A \<^bold>\<rightarrow> B \<^bold>\<and> B \<^bold>\<rightarrow> A"

(*In fact, propositions in our logic correspond to sets of worlds. 
  We introduce a convenient type alias for propositions: *)
type_synonym \<sigma> = "Set(w)" (*the type of propositions*)

(*We encode the set of valid (resp. unsatisfiable, satisfiable) propositions *)
abbreviation valid::"Set(\<sigma>)" ("\<Turnstile>_")  (* remember: Set(\<sigma>) =  \<sigma> \<Rightarrow> o *) 
  where   "\<Turnstile> A \<equiv> \<forall>A"
abbreviation unsatisfiable::"Set(\<sigma>)" ("\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t_")
  where "\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t A \<equiv> \<not>\<exists>A"
abbreviation satisfiable::"Set(\<sigma>)" ("\<Turnstile>\<^sup>s\<^sup>a\<^sup>t_")
  where  "\<Turnstile>\<^sup>s\<^sup>a\<^sup>t A \<equiv> \<not>\<Turnstile>\<^sup>u\<^sup>n\<^sup>s\<^sup>a\<^sup>t A"

(*We encode the logical consequence (endo)relations. In modal logic they come in two flavours: *)
abbreviation local_consequence::"ERel(\<sigma>)" ("[_ \<Turnstile> _]") (* remember: ERel(\<sigma>) = \<sigma> \<Rightarrow> \<sigma> \<Rightarrow> o *)
  where "[A \<Turnstile> B] \<equiv> A \<subseteq> B"
abbreviation global_consequence::"ERel(\<sigma>)" ("[_ \<Turnstile>\<^sub>g _]")
  where "[A \<Turnstile>\<^sub>g B] \<equiv> \<Turnstile> A \<rightarrow> \<Turnstile> B"

(**Seeing predicates as indexed propositions, we can 'lift' quantifiers appropriately*)  
definition qforall::"'a-Index(\<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<forall>_" [55]56) (* type ('a \<Rightarrow> \<sigma>) \<Rightarrow> \<sigma> *)
  where "\<^bold>\<forall>P \<equiv> \<lambda>w. \<forall>x. (P x) w"
definition qexists::"'a-Index(\<sigma>) \<Rightarrow> \<sigma>" ("\<^bold>\<exists>_" [55]56) 
  where "\<^bold>\<exists>P \<equiv> \<lambda>w. \<exists>x. (P x) w"

(**We conveniently introduce binder notation for the 'lifted' quantifiers above: *)
notation qforall (binder"\<^bold>\<forall>"[55]56)
notation qexists (binder"\<^bold>\<exists>"[55]56)

(******* Examples ********)
lemma "\<Turnstile> A \<^bold>\<and> B \<^bold>\<rightarrow>  A"
  by (simp add: compl_def inter_def union_def)

consts one::nat ("\<one>")
consts two::nat ("\<two>")
(*and so on...*)

lemma "\<Turnstile> \<^bold>\<forall>x. \<^bold>\<box>\<^sup>\<one>(A x) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<one>(\<^bold>\<forall>x. A x)"
  by (metis compl_def iBox_def qforall_def union_def)
lemma "\<Turnstile> (\<^bold>\<box>\<^sup>\<two>A \<^bold>\<and> \<^bold>\<box>\<^sup>\<two>A) \<^bold>\<rightarrow> \<^bold>\<box>\<^sup>\<two>A" 
  by (simp add: compl_def inter_def union_def)

end