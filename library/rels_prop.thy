(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory rels_prop (* Properties of relations *)
imports rels funcs_prop
begin


subsection \<open>Properties of relations\<close>

(*The 'defined' elements in R's domain (aka. 'domain of definition') are those elements related 
  by R to at least one element (i.e. have a non-empty image under R) *)
abbreviation(input) defined::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "defined R \<equiv> \<lambda>a. \<exists>(R a)"

lemma "defined R = relRange (R)\<^sup>T" unfolding rel_defs combs ..

(*A relation R is called 'total' (aka. 'serial' for endorelations) when it is defined for all elements
 in its domain. This definition can also be restricted to a subset A of R's domain. *)
definition totalRel::"Set(Rel('a,'b))"
  where \<open>totalRel R \<equiv> \<forall>(defined R)\<close>
definition totalRel_restr::"Set('a) \<Rightarrow> Set(Rel('a,'b))" ("totalRel[_]")
  where \<open>totalRel[A] R \<equiv> A \<subseteq> defined R\<close>

declare totalRel_def[rel_defs] totalRel_restr_def[rel_defs]

lemma totalRel_simp: "totalRel[\<UU>] R = totalRel R" unfolding rel_defs set_defs by simp

(*Analogous to functions, relations can be 'surjective' (wrt. subsets A/B of their domain/codomain)*)
definition surjectiveRel::"Set(Rel('a,'b))"
  where "surjectiveRel R \<equiv> \<forall>b. \<exists>a. R a b"
definition surjectiveRel_restr::"Set('a) \<Rightarrow> Set('b) \<Rightarrow>  Set(Rel('a,'b))" ("surjectiveRel[_,_]")
  where "surjectiveRel[A,B] R \<equiv> B \<subseteq> relImage R A"

declare surjectiveRel_def[rel_defs] surjectiveRel_restr_def[rel_defs]

lemma surjectiveRel_simp1: "surjectiveRel[\<UU>,\<UU>] R = surjectiveRel R" 
  unfolding rel_defs set_defs by simp
lemma surjectiveRel_simp2: \<open>surjectiveRel[\<UU>,B] R = totalRel[B] (R)\<^sup>T\<close> 
  unfolding rel_defs set_defs combs by simp

(*The 'determined' elements in R's domain are those for which R 'behaves deterministically', that is
 determined elements are related/mapped by R to at most one element. *)
abbreviation(input) determined::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "determined R \<equiv> \<lambda>a. \<exists>\<^sub>\<le>\<^sub>1(R a)"

(*A relation R is called 'deterministic' or 'partially-functional' wrt (a subset A of) its domain 
 when R behaves deterministically everywhere in (the subset A of) its domain. *)
definition deterministicRel::"Set(Rel('a,'b))"
  where \<open>deterministicRel R \<equiv> \<forall>(determined R)\<close>
definition deterministicRel_restr::"Set('a) \<Rightarrow> Set(Rel('a,'b))" ("deterministicRel[_]")
  where \<open>deterministicRel[A] R \<equiv> A \<subseteq> determined R\<close>

declare deterministicRel_def[rel_defs] deterministicRel_restr_def[rel_defs]


(*Analogous to functions, relations can be 'injective' (wrt. subsets A/B of their domain/codomain)*)
definition injectiveRel::"Set(Rel('a,'b))"
  where "injectiveRel R \<equiv> \<forall>b. \<exists>\<^sub>\<le>\<^sub>1a. R a b"
definition injectiveRel_restr::"Set('a) \<Rightarrow> Set('b) \<Rightarrow>  Set(Rel('a,'b))" ("injectiveRel[_,_]")
  where "injectiveRel[A,B] R \<equiv> \<forall>b. B b \<rightarrow> \<exists>\<^sub>\<le>\<^sub>1(A \<inter> (R)\<^sup>T b)"

declare injectiveRel_def[rel_defs] injectiveRel_restr_def[rel_defs]

lemma injectiveRel_simp1: "injectiveRel[\<UU>,\<UU>] R = injectiveRel R" 
  unfolding rel_defs set_defs combs by (meson Uniq_def)
lemma injectiveRel_simp2: \<open>injectiveRel[\<UU>,B] R = deterministicRel[B] (R)\<^sup>T\<close> 
  unfolding rel_defs set_defs by simp

(*Some miscelaneous characterizations*)
lemma "surjectiveRel R = (\<Inter>(funRange (\<midarrow>\<^sup>rR)) = \<emptyset>)"
  unfolding biginter_def compl_def funRange_def surjectiveRel_def by metis
lemma "totalRel R = (\<UU> \<subseteq> relPreimage (R) \<UU>)"
  by (simp add: relPreimage_def subset_def totalRel_def)

lemma "injectiveRel R = ((\<noteq>) \<subseteq>\<^sup>r (\<lambda>x y. \<UU> \<subseteq> (\<midarrow>\<^sup>rR x) \<union> (\<midarrow>\<^sup>rR y)))" oops
lemma "(injectiveRel R) = (((\<noteq>) \<inter>\<^sup>r (\<lambda>x y. (R x) \<inter> (R y) \<noteq> \<emptyset>)) = \<emptyset>\<^sup>r)" oops
lemma "deterministicRel R = (\<forall>x y. x \<noteq> y \<longrightarrow> (R)\<^sup>T x \<inter> (R)\<^sup>T y = \<emptyset>)" oops


subsection \<open>From functions to relations (and viceversa)\<close>

lemma "surjectiveFun[\<UU>,B] f = totalRel[B] [f]\<inverse>"
  unfolding func_defs set_defs rel_defs by simp
lemma "surjectiveFun f = totalRel [f]\<inverse>"
  unfolding func_defs rel_defs ..
lemma "injectiveFun f = deterministicRel [f]\<inverse>"
  unfolding func_defs rel_defs set_defs by auto


(*Every function can be lifted to a (special kind of) relation via the following definition*)
definition toRel::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" ("[_]\<^sup>R")
  where "[f]\<^sup>R \<equiv> \<lambda>a. {f a}"

declare toRel_def[rel_defs]

(*The corresponding lifted relation is always total and deterministic: *)
lemma "totalRel [f]\<^sup>R" unfolding rel_defs set_defs by simp
lemma "deterministicRel [f]\<^sup>R" unfolding rel_defs set_defs by simp

(*The two previous ways of lifting functions to relations are in fact closely related: *)
lemma \<open>[f]\<inverse> = ([f]\<^sup>R)\<^sup>T\<close>
  unfolding rel_defs combs ..

(*The inverse of a function (qua relation) is always injective and surjective*)
lemma "injectiveRel [f]\<inverse>" unfolding rel_defs by (simp add: Uniq_def)
lemma "surjectiveRel [f]\<inverse>" unfolding rel_defs by (simp add: Uniq_def)

(*The inverse of a function gets its name from the following property of injective functions:*)
lemma "injectiveFun f \<Longrightarrow> \<iota> \<circ> [f]\<inverse> \<circ> f = ID"
  unfolding func_defs rel_defs combs by (simp add: the_equality)

(*The previous property motivates introducing the notion of 'inverse function' of a (bijective) function.*)
abbreviation(input) inverseFunction::"('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" ("'(_')\<inverse>")
  where "(f)\<inverse> \<equiv> \<iota> \<circ> [f]\<inverse>" (*Beware: this definition is well-behaved for bijective functions only!*)


subsection \<open>Relations to functions\<close>

(*A relation that is both deterministic and total relates each object in its domain to an unique
  object in its codomain, and thus gives rise to a function. We call such relations 'functional'.*)
definition functionalRel::"Set(Rel('a,'b))"
  where "functionalRel R \<equiv> totalRel R \<and> deterministicRel R"

declare functionalRel_def[rel_defs]

lemma functionalRel_def2: \<open>functionalRel R = (\<forall>a. \<exists>\<^sub>1(R a))\<close> 
  unfolding rel_defs set_defs combs by blast

(*Similarly, every functional (total and deterministic) relation can be converted into a function*)
definition toFun::"Rel('a,'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("[_]\<^sub>f")
  where "[R]\<^sub>f \<equiv> \<lambda>a. \<iota> b. R a b"

declare toFun_def[rel_defs]

(*This gives rise to useful simplification rules:*)
lemma funrel_simp1: "[[f]\<^sup>R]\<^sub>f = f" 
  unfolding rel_defs by simp 
lemma funrel_simp2: "functionalRel R \<Longrightarrow> [[R]\<^sub>f]\<^sup>R = R" 
  unfolding rel_defs set_defs apply (rule ext)+ by (metis theI)

declare funrel_simp1[rel_simps] funrel_simp2[rel_simps]

(*In fact*)
lemma "toRel = \<^bold>B (=)" unfolding rel_defs combs ..
lemma "toRel = \<^bold>B \<^bold>C inverse" unfolding rel_defs combs ..
lemma "toFun = \<^bold>B \<iota>" unfolding rel_defs combs ..

lemma "toRel a = ([a]\<inverse>)\<^sup>T" by (simp add: Cc_def inverse_def toRel_def)
lemma "(f)\<inverse> = toFun [f]\<inverse>" by (simp add: Bc_def toFun_def)


(*In fact, several notions for functions can be naturally stated in terms of relations, such as
  range, injectivity and surjectivity *)
lemma \<open>funRange f = relRange [f]\<^sup>R\<close>
  unfolding rel_defs func_defs combs ..
lemma \<open>injectiveFun f = injectiveRel [f]\<^sup>R\<close> 
  unfolding rel_defs func_defs using Uniq_def by auto
lemma \<open>surjectiveFun f = surjectiveRel [f]\<^sup>R\<close> 
  unfolding rel_defs func_defs by metis
lemma "injectiveFun[A] f = injectiveRel[A,\<UU>] [f]\<^sup>R"
  unfolding rel_defs func_defs set_defs combs by auto
lemma "surjectiveFun[A,B] f = surjectiveRel[A,B] [f]\<^sup>R" 
  unfolding rel_defs func_defs set_defs by auto

(*Moreover, the monoidal structure is preserved when passing from functions to relations and viceversa.
  This gives rise to useful simplification rules: *)
lemma ID_simp1: "[ID]\<^sup>R = ID\<^sup>r" 
  unfolding rel_defs combs by auto
lemma ID_simp2: "[ID\<^sup>r]\<^sub>f = ID" 
  unfolding rel_defs combs by simp
lemma comp_simp1: "[[f]\<^sup>R \<circ>\<^sup>r [g]\<^sup>R]\<^sub>f = (f \<circ> g)" 
  unfolding rel_defs combs by simp
lemma comp_simp2: "functionalRel R \<and> functionalRel T \<Longrightarrow> [[R]\<^sub>f \<circ> [T]\<^sub>f]\<^sup>R = (R \<circ>\<^sup>r T)"
  unfolding rel_defs combs by (metis (mono_tags, opaque_lifting) the_equality unique_def)

declare ID_simp1[rel_simps] ID_simp2[rel_simps] comp_simp1[rel_simps] comp_simp2[rel_simps]


end