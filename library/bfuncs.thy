(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory bfuncs (* A basic theory of binary functions *)
imports funcs pairs
begin

section \<open>Binary Functions\<close>

subsection \<open>Transforming between unary and binary functions\<close>

(*Unary functions can be lifted to binary functions via 'reverse/inverse projections', which 
  transform a unary function into a 'projected' binary function wrt. the 1st resp. 2nd argument.*) 
abbreviation (input) rproj1::\<open>('a \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)\<close> ("\<rho>\<^sub>1")
  where "\<rho>\<^sub>1 \<equiv> \<^bold>B \<^bold>K" (*or (\<^bold>B \<^bold>C) \<^bold>K*)
abbreviation (input) rproj2::\<open>('b \<Rightarrow> 'c) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c)\<close> ("\<rho>\<^sub>2")
  where "\<rho>\<^sub>2 \<equiv> \<^bold>K"

(*The definitions above behave in fact as expected *)
lemma "\<rho>\<^sub>1 = (\<lambda>f a b. f a)" unfolding combs ..
lemma "\<rho>\<^sub>2 = (\<lambda>f a b. f b)" unfolding combs ..

(*\<rho>\<^sub>1 and \<rho>\<^sub>2 are interdefinable (in  many ways) *)
lemma "\<rho>\<^sub>1 = (\<lambda>f. (\<rho>\<^sub>2 f)\<^sup>T)" unfolding combs ..
lemma "\<rho>\<^sub>1 = (\<^bold>B \<^bold>C) \<rho>\<^sub>2" unfolding combs ..
lemma "\<rho>\<^sub>1 = \<^bold>B \<rho>\<^sub>2" unfolding combs ..
lemma "\<rho>\<^sub>2 = (\<lambda>f. (\<rho>\<^sub>1 f)\<^sup>T)" unfolding combs ..
lemma "\<rho>\<^sub>2 = (\<^bold>B \<^bold>C) \<rho>\<^sub>1" unfolding combs ..


(*Conversely, binary functions can be transformed into unary functions by partial application.
 Thus, partial application (after transposing) can be employed to 'undo' the effect of \<rho>\<^sub>1 and \<rho>\<^sub>2 *)
lemma \<open>((\<rho>\<^sub>2 f)  x) = f\<close> unfolding combs ..
lemma \<open>((\<rho>\<^sub>1 f)\<^sup>T x) = f\<close> unfolding combs .. (* (g\<^sup>T x) applies x on the 2nd position*)

(*Diagonalization transforms binary into unary functions by applying twice a given argument. It's just the \<^bold>W combinator.*)
notation Wc ("\<Delta>")

lemma "\<Delta> g = (\<lambda>a. g a a)" unfolding combs ..

(**Projection and diagonalization transformations are in fact inverse to each other, in a subtle sense.*)
lemma \<open>\<Delta>(\<rho>\<^sub>1 f) = f\<close> unfolding combs ..
lemma \<open>\<Delta>(\<rho>\<^sub>2 f) = f\<close> unfolding combs ..
lemma \<open>\<rho>\<^sub>1(\<Delta> g) = g\<close> nitpick oops (*counterexample - as expected*)
lemma \<open>\<rho>\<^sub>2(\<Delta> g) = g\<close> nitpick oops (*counterexample - as expected*)

lemma diag1_simp: \<open>(\<exists>f. g = \<rho>\<^sub>1 f) \<Longrightarrow> \<rho>\<^sub>1(\<Delta> g) = g\<close> unfolding combs by auto
lemma diag2_simp: \<open>(\<exists>f. g = \<rho>\<^sub>2 f) \<Longrightarrow> \<rho>\<^sub>2(\<Delta> g) = g\<close> unfolding combs by auto

named_theorems bfunc_simps
declare diag1_simp[bfunc_simps] diag2_simp[bfunc_simps]


section \<open>Correspondence between operations on pairs and operations on binary functions\<close>

(*Reverse-projections and pair-projections correspond to each other as expected*)
lemma rproj1_simp: "\<lceil>\<rho>\<^sub>1 f\<rceil> \<langle>x,y\<rangle> = f x" unfolding combs unfolding uncurry_def proj1_simp ..
lemma rproj2_simp: "\<lceil>\<rho>\<^sub>2 f\<rceil> \<langle>x,y\<rangle> = f y" unfolding combs unfolding uncurry_def proj2_simp ..
lemma rproj1_redex: "\<lceil>(\<rho>\<^sub>1 f)\<rceil> p = f (\<pi>\<^sub>1 p)" unfolding combs unfolding uncurry_def ..
lemma rproj2_redex: "\<lceil>(\<rho>\<^sub>2 f)\<rceil> p = f (\<pi>\<^sub>2 p)" unfolding combs unfolding uncurry_def ..

(*Transposition and pair-swap correspond to each other as expected:*)
lemma transp1_simp: " \<lceil>(g)\<^sup>T\<rceil> (p)\<Zcat> = \<lceil>g\<rceil> p"  unfolding combs unfolding pair_defs by simp
lemma transp2_simp: " \<lceil>(\<lfloor>f\<rfloor>)\<^sup>T\<rceil> (p)\<Zcat> = f p"  unfolding transp1_simp unfolding uncurry_simp ..
lemma transp1_redex: " \<lceil>(g)\<^sup>T\<rceil> p = \<lceil>g\<rceil> (p)\<Zcat>" unfolding combs unfolding pair_defs by simp
lemma transp2_redex: " \<lceil>(\<lfloor>f\<rfloor>)\<^sup>T\<rceil> p = f (p)\<Zcat>" unfolding transp1_redex unfolding uncurry_simp ..

declare rproj1_simp[bfunc_simps] rproj2_simp[bfunc_simps]
        transp1_simp[bfunc_simps] transp2_simp[bfunc_simps]

end