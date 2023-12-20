(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory endorels (* A basic theory of endorelations *)
imports rels
begin

subsection \<open>Special properties of (endo-)relations\<close>


(*Set of 'reflexive' ('diagonal') elements.*)
definition Reflexive::"ERel('a) \<Rightarrow> Set('a)"
  where "Reflexive R \<equiv> \<lambda>a. R a a"

(*Set of 'irreflexive elements'.*)
definition Irreflexive::"ERel('a) \<Rightarrow> Set('a)"
  where "Irreflexive R \<equiv> \<lambda>a. \<not>(R a a)"

(*An endorelation is called 'reflexive' when its set of 'reflexive elements' is the whole domain/universe
 (i.e. every element in its domain is related to itself).*)
abbreviation reflexive::"Set(ERel('a))"
  where \<open>reflexive R \<equiv> \<forall>(Reflexive R)\<close>

(*An endorelation is called 'irreflexive' when its set of 'irreflexive elements' is the whole domain/universe*)
abbreviation irreflexive::"Set(ERel('a))"
  where \<open>irreflexive R \<equiv> \<forall>(Irreflexive R)\<close>

(* Set of 'symmetric pairs' (being mutually reachable)*)
definition Symmetric::"ERel('a) \<Rightarrow> ERel('a)"
  where \<open>Symmetric R \<equiv> \<lambda>a b. R a b \<longrightarrow> R b a\<close> 

abbreviation symmetric::"Set(ERel('a))"
  where \<open>symmetric R \<equiv> \<forall>x y. (Symmetric R) x y\<close>

lemma "symmetric R = (\<forall>x y. R x y \<leftrightarrow> R y x)" by (metis Symmetric_def)

(* Set of 'asymmetric pairs' (reachability not corresponded)*)
definition Asymmetric::"ERel('a) \<Rightarrow> ERel('a)"
  where \<open>Asymmetric R \<equiv> \<lambda>a b. R a b \<rightarrow> \<not>R b a\<close> 

abbreviation asymmetric::"Set(ERel('a))"
  where \<open>asymmetric R \<equiv> \<forall>x y. (Asymmetric R) x y\<close>

abbreviation antisymmetric::"Set(ERel('a))"
  where \<open>antisymmetric R \<equiv> \<forall>x y. x \<noteq> y \<rightarrow> (Asymmetric R) x y\<close>

lemma "(irreflexive R \<and> antisymmetric R) = asymmetric R" 
  by (metis Asymmetric_def Irreflexive_def)

(* Set of 'transitive pairs' (being indirectly reachable via some c)*)
definition Transitive::"ERel('a) \<Rightarrow> ERel('a)"
  where \<open>Transitive R \<equiv> \<lambda>a b. (\<exists>c. R a c \<and> R c b) \<rightarrow> R a b\<close>

abbreviation transitive::"Set(ERel('a))"
  where \<open>transitive R \<equiv> \<forall>x y. (Transitive R) x y\<close>

lemma transitive_char: "transitive R = (\<forall>x y z. R x y \<and> R y z \<rightarrow> R x z)" by (metis Transitive_def)


(*Right- and left-euclidean pairs*)
definition REuclidean::"ERel('a) \<Rightarrow> ERel('a)"
  where \<open>REuclidean R \<equiv> \<lambda>a b. (\<exists>c. R c a \<and> R c b) \<rightarrow> R a b\<close>

definition LEuclidean::"ERel('a) \<Rightarrow> ERel('a)"
  where \<open>LEuclidean R \<equiv> \<lambda>a b. (\<exists>c. R a c \<and> R b c) \<rightarrow> R a b\<close>

abbreviation rEuclidean::"Set(ERel('a))"
  where \<open>rEuclidean R \<equiv> \<forall>x y. (REuclidean R) x y\<close>

abbreviation lEuclidean::"Set(ERel('a))"
  where \<open>lEuclidean R \<equiv> \<forall>x y. (LEuclidean R) x y\<close>

lemma \<open>rEuclidean R = (\<forall>a b c. R c a \<and> R c b \<rightarrow> R a b)\<close> by (simp add: REuclidean_def) 


abbreviation "preorder R \<equiv> reflexive R \<and> transitive R"
abbreviation "partial_order R \<equiv> preorder R \<and> antisymmetric R"
definition "equivalence R \<equiv> preorder R \<and> symmetric R"

lemma "reflexive R \<and> transitive R \<and> symmetric R \<rightarrow> rEuclidean R"
  by (metis REuclidean_def Symmetric_def Transitive_def)


subsection \<open>Inter-relating properties of relations\<close>

(*Exercise: Prove or disprove *)

end