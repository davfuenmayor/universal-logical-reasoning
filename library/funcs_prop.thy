(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory funcs_prop (* Properties of functions *)
imports funcs sets
begin

subsection \<open>Properties of functions\<close>

(*The set of injective functions (restricted wrt. domain-set A)*)
definition injectiveFun::"Set('a \<Rightarrow> 'b)"
  where "injectiveFun f \<equiv> \<forall>a\<^sub>1 a\<^sub>2. (f a\<^sub>1) = (f a\<^sub>2) \<rightarrow> a\<^sub>1 = a\<^sub>2"
definition injectiveFun_restr::"Set('a) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("injectiveFun[_]")
  where "injectiveFun[A] f \<equiv> \<forall>a\<^sub>1 a\<^sub>2. A a\<^sub>1 \<and> A a\<^sub>2 \<rightarrow> (f a\<^sub>1) = (f a\<^sub>2) \<rightarrow> a\<^sub>1 = a\<^sub>2"

(*The set of surjective functions (restricted wrt. domain-set A and codomain-set B)*)
definition surjectiveFun::"Set('a \<Rightarrow> 'b)"
  where "surjectiveFun f \<equiv> \<forall>b. \<exists>a. f a = b"
definition surjectiveFun_restr::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("surjectiveFun[_,_]")
  where "surjectiveFun[A,B] f \<equiv> \<forall>b. B b \<rightarrow> (\<exists>a. A a \<and> f a = b)"

abbreviation "bijectiveFun f \<equiv> injectiveFun f \<and> surjectiveFun f"

declare injectiveFun_def[func_defs] injectiveFun_restr_def[func_defs]
        surjectiveFun_def[func_defs] surjectiveFun_restr_def[func_defs]

lemma injectiveFun_univ[func_simps]: "injectiveFun[\<UU>] f = injectiveFun f" unfolding func_defs by simp
lemma surjectiveFun_univ[func_simps]: "surjectiveFun[\<UU>,\<UU>] f = surjectiveFun f" unfolding func_defs by simp

(**The set of map(ping)s from domain-set A *into* codomain-set B.*)
definition map::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("map[_,_]")
  where "map[A,B] f \<equiv> \<forall>a. A a \<rightarrow> B (f a)"

lemma map_def2: "map[A,B] f = ((funImage f A) \<subseteq> B)" 
  by (metis (mono_tags, lifting) funImage_def map_def subset_def)

(**The set of surjective map(ping)s from domain-set A *onto* a codomain-set B.*)
definition surjectiveMap::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("surjectiveMap[_,_]")
  where "surjectiveMap[A,B] f \<equiv> (\<lambda>b. \<exists>a. A a \<and> f a = b) = B"

declare map_def[func_defs] surjectiveMap_def[func_defs]

lemma surjectiveMap_simpdef: "surjectiveMap[A,B] f = (map[A,B] f \<and> surjectiveFun[A,B] f)" 
  unfolding func_defs by auto

abbreviation(input) injectiveMap ("injectiveMap[_,_]") (*aka. embedding*) 
  where "injectiveMap[A,B] f \<equiv> map[A,B] f \<and> injectiveFun[A] f"

definition bijectiveMap ("bijectiveMap[_,_]")
  where "bijectiveMap[A,B] f \<equiv> surjectiveMap[A,B] f \<and> injectiveFun[A] f"

declare bijectiveMap_def[func_defs]

(*Beware: a bijective map (wrt A and B) is not just a function that is injective and surjective (wrt A and B)*)
lemma "bijectiveMap[A,B] f = (injectiveFun[A] f \<and> surjectiveFun[A,B] f)"
  nitpick oops (*counterexample*)

lemma bijectiveMap_simp[func_simps]: "bijectiveMap[\<UU>,\<UU>] f = bijectiveFun f"
  unfolding bijectiveMap_def surjectiveMap_simpdef func_defs by auto

(*Properties of function composition*)
lemma surjective_comp: "surjectiveFun[A,B] f \<Longrightarrow> surjectiveFun[B,C] g \<Longrightarrow> surjectiveFun[A,C] (g \<circ> f)"
  unfolding surjectiveFun_restr_def Bc_def by (smt (z3))

lemma map_comp: "map[A,B] f \<Longrightarrow> map[B,C] g \<Longrightarrow> map[A,C] (g \<circ> f)" 
  by (simp add: Bc_def map_def)

lemma injectiveMap_comp: "injectiveMap[A,B] f \<Longrightarrow> injectiveMap[B,C] g \<Longrightarrow> injectiveMap[A,C] (g \<circ> f)" 
  by (simp add: Bc_def injectiveFun_restr_def map_def)

lemma surjectiveMap_comp: "surjectiveMap[A,B] f \<Longrightarrow> surjectiveMap[B,C] g \<Longrightarrow> surjectiveMap[A,C] (g \<circ> f)" 
  unfolding surjectiveMap_simpdef using map_comp surjective_comp by blast


(*Further interesting lemmata*)

(*If A can be mapped injectively (embedded) into B then B can be mapped onto A (assuming A non-empty)
Proof idea: Starting with an injection f from A into B, construct an (surjective) map g from 
 B onto A, recalling that for x \<in> B we have that f\<inverse>(x) \<inter> A is either:
  (1) a singleton: take g(x) = \<iota>x.f\<inverse>(x) (because f is injective wrt A)
  (2) empty: take g(x) = c for an arbitrary c \<in> A (since A is non-empty)  *)
lemma inj_to_surj_map: "\<exists>A \<Longrightarrow> \<exists>f. injectiveMap[A,B] f \<Longrightarrow> \<exists>g. surjectiveMap[B,A] g" 
  sorry (*TODO: exercise*)

(*If A can be mapped onto B then B can be mapped injectively (embedded) into A
Proof idea: Start with a map f from A onto B, let g' be the (injective) map from B onto A/kernel(f).
 Define g as the composition of g' with the function (\<epsilon>) that maps each equivalence class in A/kernel(f)
 to its representative. Being the composition of two injections, g is also an injection.*)
lemma surj_to_inj_map: "\<exists>f. surjectiveMap[A,B] f \<Longrightarrow> \<exists>g. injectiveMap[B,A] g"
  sorry (*TODO: exercise*)

(*Cantor-Schroeder-Bernstein theorem: If two sets can be mapped injectively into each other then there
 exists a bijection between them.
Proof idea: Follows as a corollary to the Banach Decomposition Theorem, which can itself be proven
 using the Knaster-Tarski fixed point theorem. *)
lemma inj_to_bij_map: "\<exists>f. injectiveMap[A,B] f \<Longrightarrow> \<exists>g. injectiveMap[B,A] g \<Longrightarrow> \<exists>h. bijectiveMap[A,B] h" 
  sorry (*TODO: exercise*)


end