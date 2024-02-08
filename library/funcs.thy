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
definition fRange::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b)"
  where "fRange f \<equiv> \<lambda>b. \<exists>a. f a = b"

(*We can 'lift' functions to act on sets via the "image" operator.
  Read "fImage f A" as "the (functional) image of A under f".*)
definition fImage::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "fImage f \<equiv> \<lambda>A. \<lambda>b. \<exists>a. A a \<and> f a = b"

(*Analogously, we have the "preimage" (aka. "inverse-image") operator.
  Read "fPreimage f B" as "the (functional) preimage of B under f".*)
definition fPreimage::"('a \<Rightarrow> 'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)"
  where "fPreimage f \<equiv> \<lambda>B. \<lambda>a. B (f a)"

lemma fImage_morph1: "fImage (f \<circ> g) = (fImage f) \<circ> (fImage g)" 
  unfolding fImage_def combs by auto
lemma fImage_morph2: "fImage ID = ID" 
  unfolding fImage_def combs by simp
lemma fPreimage_nmorph1: "fPreimage (f \<circ> g) = (fPreimage g) \<circ> (fPreimage f)" 
  unfolding fPreimage_def combs ..
lemma fPreImage_nmorph2: "fPreimage ID = ID" unfolding fPreimage_def combs ..

declare fRange_def[func_defs] fImage_def[func_defs] fPreimage_def[func_defs]

(*Convenient notation for the image/preimage of a set under a function*)
notation(input) fImage ("\<lbrakk>_ _\<rbrakk>") and fPreimage ("\<lbrakk>_ _\<rbrakk>\<inverse>")

(*Just for fun: we paraphrase image, preimage, and range of a function using combinators *)
lemma "fImage = (\<^bold>B \<^bold>C) (\<^bold>B (\<^bold>B (\<^bold>B ((\<noteq>) (\<^bold>K False)))) ((\<^bold>B (\<^bold>B \<^bold>S)) ((\<^bold>B (\<^bold>B (\<^bold>B (\<and>)))) (\<^bold>C ((\<^bold>B \<^bold>B) (=))))))"
  unfolding combs func_defs by metis
lemma "fPreimage = \<^bold>C \<^bold>B" 
  unfolding combs func_defs ..
lemma "fRange = \<^bold>C fImage (\<lambda>x. \<top>)"
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

(**The set of mappings from domain-set A *into* codomain-set B.*)
definition mapping::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("mapping[_,_]")
  where "mapping[A,B] f \<equiv> \<forall>a. A a \<rightarrow> B (f a)"

(**The set of mappings from domain-set A *onto* a codomain-set B.*)
definition mappingOnto::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("mappingOnto[_,_]")
  where "mappingOnto[A,B] f \<equiv> (\<lambda>b. \<exists>a. A a \<and> f a = b) = B"

declare mapping_def[func_defs] mappingOnto_def[func_defs]

lemma mappingOnto_simpdef: "mappingOnto[A,B] f = (mapping[A,B] f \<and> surjectiveFun[A,B] f)" 
  unfolding func_defs by auto

abbreviation(input) embeddingMap ("embeddingMap[_,_]") 
  where "embeddingMap[A,B] f \<equiv> mapping[A,B] f \<and> injectiveFun[A] f"

definition bijectiveMap ("bijectiveMap[_,_]")
  where "bijectiveMap[A,B] f \<equiv> mappingOnto[A,B] f \<and> injectiveFun[A] f"

declare bijectiveMap_def[func_defs]

(*Beware: a bijective map (wrt A and B) is not just a function that is injective and surjective (wrt A and B)*)
lemma "bijectiveMap[A,B] f = (injectiveFun[A] f \<and> surjectiveFun[A,B] f)"
  nitpick oops (*counterexample*)

lemma bijectiveMap_simp[func_simps]: "bijectiveMap[\<UU>,\<UU>] f = bijectiveFun f"
  unfolding bijectiveMap_def mappingOnto_simpdef func_defs by auto


end