(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory pairs (* A basic theory of (endo)pairs *)
imports types
begin


section \<open>Pairs\<close>

(*Let's put pair-related definitions/simplification-rules in two bags ("pair_defs" resp. "pair_simps") *)
named_theorems pair_defs 
named_theorems pair_simps

(*Term constructor: making pairs out of objects*)
definition mkPair::"'a \<Rightarrow> 'a \<Rightarrow> Pair('a)" ("\<langle>_,_\<rangle>") 
  where  "\<langle>x,y\<rangle> \<equiv> \<lambda>b. if b then x else y"

(*Under the hood, the term constructor mkPair is built in terms of definite descriptions: *)
lemma "\<langle>x,y\<rangle> = (\<lambda>b. \<iota> z. (b \<rightarrow> z = x) \<and> (\<not>b \<rightarrow> z = y))" 
  unfolding mkPair_def unfolding If_def by simp

(*Incidentally, pairs of booleans have an alternative, simpler representation: *)
lemma mkPair_booldef: "\<langle>x,y\<rangle> = (\<lambda>b. (b \<and> x) \<or> (\<not>b \<and> y))" 
  unfolding mkPair_def apply(rule ext) by simp

(*Add the previous definitions into the "pair_defs" bag*)
declare mkPair_def[pair_defs] mkPair_booldef [pair_defs]

(*Now, observe that*)
lemma "\<langle>x,y\<rangle> \<top> = x" 
  unfolding mkPair_def by simp
lemma "\<langle>x,y\<rangle> \<bottom> = y" 
  unfolding mkPair_def by simp

(*This motivates the introduction of the following projection/extraction functions*)
definition proj1::"Pair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>1")
  where "\<pi>\<^sub>1 \<equiv> \<lambda>P. P \<top>"
definition proj2::"Pair('a) \<Rightarrow> 'a" ("\<pi>\<^sub>2")
  where "\<pi>\<^sub>2 \<equiv> \<lambda>P. P \<bottom>"

declare proj1_def[pair_defs] proj2_def[pair_defs]

(*The following lemmata ("product laws") verify that the previous definitions work as intended. 
  The names of lemmata suggest that they are useful as simplification rules*)
lemma proj1_simp: "\<pi>\<^sub>1\<langle>x,y\<rangle> = x" 
  unfolding pair_defs by simp
lemma proj2_simp: "\<pi>\<^sub>2\<langle>x,y\<rangle> = y" 
  unfolding pair_defs by simp
lemma mkPair_simp: "\<langle>\<pi>\<^sub>1 P, \<pi>\<^sub>2 P\<rangle> = P" 
  unfolding pair_defs apply(rule ext) by simp

declare proj1_simp[pair_simps] proj2_simp[pair_simps] mkPair_simp[pair_simps]

(*Let's now add the useful 'swap' operation on pairs*)
definition swapPair::"Pair('a) \<Rightarrow> Pair('a)" ("'(_')\<Zcat>")
  where "(p)\<Zcat> \<equiv> \<langle>\<pi>\<^sub>2 p, \<pi>\<^sub>1 p\<rangle>"

lemma swapPair_simp: "(\<langle>a, b\<rangle>)\<Zcat> = \<langle>b, a\<rangle>" 
  unfolding swapPair_def unfolding proj1_simp proj2_simp ..

(*Add definition and simplification rule to the respective bags*)
declare swapPair_def[pair_defs]
declare swapPair_simp[pair_simps]


section \<open>Isomorphism of types for binary operations\<close>

(*The two morphisms that convert functions on pairs into binary (curried) functions, and viceversa*)
definition curry::"Op\<^sub>2*('a,'b) \<Rightarrow> Op\<^sub>2('a,'b)" ("\<lfloor>_\<rfloor>"[90])
  where "curry Op \<equiv> \<lambda>x y. Op\<langle>x,y\<rangle>"
definition uncurry::"Op\<^sub>2('a,'b) \<Rightarrow> Op\<^sub>2*('a,'b)" ("\<lceil>_\<rceil>"[91])
  where "uncurry Op \<equiv> \<lambda>P. Op (\<pi>\<^sub>1 P) (\<pi>\<^sub>2 P)"

(*Both morphisms constitute an isomorphism (we tag them as simplification rules too)*)
lemma   curry_simp: "\<lfloor>\<lceil>Op\<rceil>\<rfloor> = Op" 
  unfolding curry_def uncurry_def unfolding proj1_simp proj2_simp .. 
lemma uncurry_simp: "\<lceil>\<lfloor>Op\<rfloor>\<rceil> = Op"
  unfolding curry_def uncurry_def unfolding mkPair_simp ..

declare curry_def[pair_defs] uncurry_def[pair_defs] 
        curry_simp[pair_simps] uncurry_simp[pair_simps]

end