(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory funcs (* A basic theory of functions *)
imports types combinators
begin

section \<open>Functions\<close>

(*Let's put function-related definitions/simplification-rules in two bags ("func_defs" resp. "func_simps") *)
named_theorems func_defs
named_theorems func_simps


subsection \<open>Algebraic structure\<close>

subsubsection \<open>Monoidal structure\<close>
(*Function composition is the main binary operation between functions. It corresponds to the \<^bold>B combinator.*)
notation Bc (infixl "\<circ>" 75)
(*The identity function can be seen as a 0-ary operation (i.e. a 'constant'). It corresponds to the \<^bold>I combinator.*)
notation Ic ("ID")

(*Recalling*)
lemma "f \<circ> g = (\<lambda>x. f (g x))" unfolding combs ..

(*Composition and identity satisfy the monoid conditions.*)
lemma "(f \<circ> g) \<circ> h = f \<circ> (g \<circ> h)" unfolding combs ..    (* associativity *)
lemma "ID \<circ> f = f" unfolding combs ..                   (* left identity *)
lemma "f \<circ> ID = f" unfolding combs ..                   (* right identity *)

subsubsection \<open>Transposition\<close>
(*Transposition flips/swaps the arguments of a (curried) binary function. It corresponds to the \<^bold>C combinator*)
notation Cc ("'(_')\<^sup>T")

lemma "(f)\<^sup>T = (\<lambda>a b. f b a)" unfolding combs .. (*swaps arguments*)

(*Transposition is clearly an involution.*)
lemma "((f)\<^sup>T)\<^sup>T = f" unfolding combs ..


subsection \<open>Range, image & preimage of functions\<close>

(*Given a function f we can obtain its (functional) range as the set of those objects 'b' in the 
 codomain that are the image of some object 'a' (i.e. have a non-empty preimage) under the function f.*)
definition funRange::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "funRange f \<equiv> \<lambda>b. \<exists>a. f a = b"

(*We can 'lift' functions to act on sets via the "image" operator.
  Read "funImage f A" as "the (functional) image of A under f".*)
definition funImage::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "funImage f \<equiv> \<lambda>A. \<lambda>b. \<exists>a. A a \<and> f a = b"

(*Analogously, we have the "preimage" (aka. "inverse-image") operator.
  Read "funPreimage f B" as "the (functional) preimage of B under f".*)
definition funPreimage::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)"
  where "funPreimage f \<equiv> \<lambda>B. \<lambda>a. B (f a)"

lemma funImage_morph1: "funImage (f \<circ> g) = (funImage f) \<circ> (funImage g)" 
  unfolding funImage_def combs by auto
lemma funImage_morph2: "funImage ID = ID" 
  unfolding funImage_def combs by simp
lemma funPreimage_nmorph1: "funPreimage (f \<circ> g) = (funPreimage g) \<circ> (funPreimage f)" 
  unfolding funPreimage_def combs ..
lemma funPreimage_nmorph2: "funPreimage ID = ID" unfolding funPreimage_def combs ..

declare funRange_def[func_defs] funImage_def[func_defs] funPreimage_def[func_defs]

(*Convenient notation for the image/preimage of a set under a function*)
notation funImage ("\<lbrakk>_ _\<rbrakk>") and funPreimage ("\<lbrakk>_ _\<rbrakk>\<inverse>")

(*Just for fun: we paraphrase image, preimage, and range of a function using combinators *)
lemma "funImage = (\<^bold>B \<^bold>C) (\<^bold>B (\<^bold>B (\<^bold>B ((\<noteq>) (\<^bold>K False)))) ((\<^bold>B (\<^bold>B \<^bold>S)) ((\<^bold>B (\<^bold>B (\<^bold>B (\<and>)))) (\<^bold>C ((\<^bold>B \<^bold>B) (=))))))"
  unfolding combs func_defs by metis
lemma "funPreimage = \<^bold>C \<^bold>B" 
  unfolding combs func_defs ..
lemma "funRange = \<^bold>C funImage (\<lambda>x. \<top>)"
  unfolding combs func_defs by simp


subsection \<open>Properties of functions\<close>

(*Two useful functions with boolean codomain: The "universal" and the "empty" set.*)
abbreviation(input) univ::"Set('a)" ("\<UU>")
  where "\<UU> \<equiv> \<lambda>x. \<top>"
abbreviation(input) empty::"Set('a)" ("\<emptyset>")
  where "\<emptyset> \<equiv> \<lambda>x. \<bottom>"

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