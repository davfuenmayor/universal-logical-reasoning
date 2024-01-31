(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory pairs (* A basic theory of (endo)pairs *)
imports types
begin


section \<open>Pairs\<close>

(*Let's put pair-related simplification-rules in a bag (and call it "pair_simps") *)
named_theorems pair_simps

(*Term constructor: making pairs out of objects*)
definition mkPair::"'a \<Rightarrow> 'a \<Rightarrow> Pair('a)" ("\<langle>_,_\<rangle>") 
  where  "\<langle>x,y\<rangle> \<equiv> \<lambda>b. if b then x else y"

(*Under the hood, the term constructor mkPair is built in terms of definite descriptions: *)
lemma "\<langle>x,y\<rangle> = (\<lambda>b. \<iota> z. (b \<rightarrow> z = x) \<and> (\<not>b \<rightarrow> z = y))" 
  unfolding If_def mkPair_def by simp

(*Incidentally, pairs of booleans have an alternative, simpler representation: *)
lemma mkPair_bool[pair_simps]: "\<langle>x,y\<rangle> = (\<lambda>b. (b \<and> x) \<or> (\<not>b \<and> y))" 
  apply(rule ext) unfolding mkPair_def by simp

(*Now, observe that*)
lemma "\<langle>x,y\<rangle> \<top> = x" unfolding mkPair_def by simp
lemma "\<langle>x,y\<rangle> \<bottom> = y" unfolding mkPair_def by simp

(*This motivates the introduction of the following projection/extraction functions*)
abbreviation proj1::"Pair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>1")
  where "\<pi>\<^sub>1 \<equiv> \<lambda>P. P \<top>"
abbreviation proj2::"Pair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>2")
  where "\<pi>\<^sub>2 \<equiv> \<lambda>P. P \<bottom>"

(*The following lemmata ("product laws") verify that the previous definitions work as intended. 
  The names of lemmata suggest that they are useful as simplification rules*)
lemma proj1_char[pair_simps]: "\<pi>\<^sub>1\<langle>x,y\<rangle> = x" unfolding mkPair_def by simp
lemma proj2_char[pair_simps]: "\<pi>\<^sub>2\<langle>x,y\<rangle> = y" unfolding mkPair_def by simp
lemma mkPair_char[pair_simps]: "\<langle>\<pi>\<^sub>1 P, \<pi>\<^sub>2 P\<rangle> = P" apply(rule ext) unfolding mkPair_def by simp

(*Let's now add the useful 'swap' (endo-)operation on pairs*)
abbreviation swapPair::"EOp(Pair('a))" ("'(_')\<Zcat>")
  where "(p)\<Zcat> \<equiv> \<lambda>b. p (\<not>b)"

lemma swapPair_char[pair_simps]: "(\<langle>a, b\<rangle>)\<Zcat> = \<langle>b, a\<rangle>" unfolding mkPair_def by auto
lemma swapPair_simp[pair_simps]: "\<langle>\<pi>\<^sub>2 p, \<pi>\<^sub>1 p\<rangle> = (p)\<Zcat>" unfolding mkPair_def by auto


section \<open>Isomorphism of types for binary operations\<close>

(*The two morphisms that convert functions on pairs into binary (curried) functions, and viceversa*)
definition curry::"Op\<^sub>2*('a,'b) \<Rightarrow> Op\<^sub>2('a,'b)" ("\<lfloor>_\<rfloor>"[90])
  where "curry Op \<equiv> \<lambda>x y. Op\<langle>x,y\<rangle>"
definition uncurry::"Op\<^sub>2('a,'b) \<Rightarrow> Op\<^sub>2*('a,'b)" ("\<lceil>_\<rceil>"[91])
  where "uncurry Op \<equiv> \<lambda>P. Op (\<pi>\<^sub>1 P) (\<pi>\<^sub>2 P)"

(*Both morphisms constitute an isomorphism (we tag them as simplification rules too)*)
lemma curry_iso1[pair_simps]: "\<lfloor>\<lceil>Op\<rceil>\<rfloor> = Op" 
  unfolding curry_def uncurry_def unfolding proj1_char proj2_char ..
lemma curry_iso2[pair_simps]: "\<lceil>\<lfloor>Op\<rfloor>\<rceil> = Op"
  unfolding curry_def uncurry_def unfolding mkPair_char ..

end