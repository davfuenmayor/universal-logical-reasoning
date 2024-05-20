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

end