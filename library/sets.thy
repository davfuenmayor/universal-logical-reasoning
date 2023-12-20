(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory sets (*  A basic theory of sets  *)
imports funcs
begin

section \<open>Sets\<close>

(*Let's put set-related definitions/simplification-rules in two bags ("set_defs" resp. "set_simps") *)
named_theorems set_defs
named_theorems set_simps


subsection \<open>Constructing sets\<close>

(*By extension/enumeration:*)
abbreviation(input) oneElem::"'a \<Rightarrow> Set('a)" ("{_}")
  where \<open>{a} \<equiv> \<lambda>x. x = a\<close>  (* i.e. (=)a *)
  (* where \<open>{a} \<equiv> \<lambda>x. a = x\<close>  (* i.e. (=)a *) *)
abbreviation(input) twoElem::"'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("{_,_}")
  where \<open>{a,b} \<equiv> \<lambda>x. a = x \<or> b = x\<close>
abbreviation(input) threeElem::"'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> Set('a)" ("{_,_,_}")
  where \<open>{a,b,c} \<equiv> \<lambda>x. a = x \<or> b = x \<or> c = x\<close>

(*By comprehension: Write "imageFun (\<lambda>x. t\<^sub>x) S" for "{ t\<^sub>x | x in S }" (where x is free in term t\<^sub>x)
 For example: *)
lemma "(fImage (\<lambda>x::int. 2*x) {1,2,3}) = {2,4,6}" (*corresponds to { 2*x | x in {1,2,3} } *)
  unfolding fImage_def by auto


subsection \<open>Basic Predicates\<close>

(*Recalling HOL quantification, we note that "\<forall>A" means that the set A contains all alements*)
lemma "\<forall>A = (\<forall>x. A x)" ..
(*Analogously, "\<exists>A" means: A contains at least one element, i.e. A is nonempty*)
lemma "\<exists>A = (\<exists>x. A x)" ..

(*Verify well-known characterizations for set quantifiers*)
lemma All_intro2simp: "(A = \<UU>) = \<forall>A" unfolding All_def ..
lemma Ex_intro2simp:  "(A \<noteq> \<emptyset>) = \<exists>A" by auto

(*Let's put set-related simplification rules in the "set_simps" bag *)
declare All_intro2simp[set_simps] Ex_intro2simp[set_simps]

(* "\<exists>\<^sub>\<le>\<^sub>1 A" means: A contains at most one element (A may be empty)*)
definition unique::"Set(Set('a))" ("\<exists>\<^sub>\<le>\<^sub>1")
  where \<open>\<exists>\<^sub>\<le>\<^sub>1A \<equiv> \<forall>x y. A x \<and> A y \<rightarrow> x = y\<close>
(* "\<exists>\<^sub>1 A" means: A contains one single element, i.e. A is a 'singleton set'.*)
definition single::"Set(Set('a))" ("\<exists>\<^sub>1")
  where \<open>\<exists>\<^sub>1A \<equiv> \<exists>x. A x \<and> (\<forall>y. A y \<rightarrow> x = y)\<close>

declare unique_def[set_defs] single_def[set_defs]

lemma single_def2: "\<exists>\<^sub>1A = (\<exists>A \<and> \<exists>\<^sub>\<le>\<^sub>1A)" (*alternative, equivalent definition*)
  unfolding single_def unique_def by auto
lemma single_def3: "\<exists>\<^sub>1A = (\<exists>a. A = {a})" (*alternative, equivalent definition*)
  unfolding single_def2 unique_def by auto


subsection \<open>Algebraic structure\<close>

subsubsection \<open>Boolean structure\<close>
(*We introduce below some operations on sets which endow them with a Boolean algebra structure.*)

(*Set complement is a unary operation*)
definition compl::"Set('a) \<Rightarrow> Set('a)" ("\<midarrow>") (* type same as: ('a Set,'a)Rel *)
  where \<open>\<midarrow>A \<equiv> \<lambda>x. \<not>A x\<close>

(*We can also define some binary operations on sets *)
definition inter::"Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" (infixr "\<inter>" 54) 
  where "A \<inter> B \<equiv> \<lambda>x. A x \<and> B x"
definition union::"Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" (infixr "\<union>" 53) 
  where "A \<union> B \<equiv> \<lambda>x. A x \<or> B x"
definition  diff::"Set('a) \<Rightarrow> Set('a) \<Rightarrow> Set('a)" (infixr "\<leftharpoonup>" 51) 
  where "A \<leftharpoonup> B \<equiv> \<lambda>x. A x \<and> \<not>B x" (** set difference*)

(*Union and intersection can be generalized to the 'infinitary' case (i.e. operating on arbitrary sets of sets)*)
definition biginter::"Set(Set('a)) \<Rightarrow> Set('a)" ("\<Inter>")
  where "\<Inter>S \<equiv> \<lambda>x. \<forall>A. S A \<rightarrow> A x"
definition bigunion::"Set(Set('a)) \<Rightarrow> Set('a)" ("\<Union>") 
  where "\<Union>S \<equiv> \<lambda>x. \<exists>A. S A  \<and>  A x"

(*Let's put set-related definitions in the "set_defs" bag *)
declare compl_def[set_defs] inter_def[set_defs] union_def[set_defs] diff_def[set_defs]
        biginter_def[set_defs] bigunion_def[set_defs]

lemma deMorganAll_simp: "(\<not>\<exists>(\<midarrow>A)) = \<forall>A" unfolding compl_def by simp
lemma deMorganEx_simp: "(\<not>\<forall>(\<midarrow>A)) = \<exists>A" unfolding compl_def by simp

declare deMorganAll_simp[set_simps] deMorganEx_simp[set_simps]


subsubsection \<open>Ordering structure\<close>

(*The algebra of sets is ordered by the standard subset (endo)relation, as defined below.*)
definition subset::"ERel(Set('a))" (infixr "\<subseteq>" 51) 
  where "A \<subseteq> B \<equiv> \<forall>x. A x \<rightarrow> B x"
abbreviation(input) superset::"ERel(Set('a))" (infixr "\<supseteq>" 51)
  where "A \<supseteq> B \<equiv> B \<subseteq> A" (*for convenience*)

definition psubset::"ERel(Set('a))" (infixr "\<subset>" 51) (*proper subset*)
  where "A \<subset> B \<equiv> A \<subseteq> B \<and> \<exists>(B \<leftharpoonup> A)"
abbreviation(input) psuperset::"ERel(Set('a))" (infixr "\<supset>" 51) (*proper superset*)
  where "A \<supset> B \<equiv> B \<subset> A" (*for convenience*)

declare subset_def[set_defs] psubset_def[set_defs]

end