(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory combinators (*  A basic theory of combinators  *)
  imports base
begin

(*Classic combinators (introduced by Schönfinkel)*)
definition Ic::"'a \<Rightarrow> 'a" ("\<^bold>I")
  where "\<^bold>I \<equiv> \<lambda>x. x"
definition Kc::"'a \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>K")
  where "\<^bold>K \<equiv> \<lambda>x y. x"
definition Cc::"('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>C")
  where "\<^bold>C \<equiv> \<lambda>f x y. (f y) x"
definition Bc::"('b \<Rightarrow> 'a) \<Rightarrow> ('c \<Rightarrow> 'b) \<Rightarrow> 'c \<Rightarrow> 'a" ("\<^bold>B")
  where "\<^bold>B \<equiv> \<lambda>f g x. f (g x)"
definition Sc::"('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>S")
  where "\<^bold>S \<equiv> \<lambda>f y w. (f w) (y w)"

(*We add some further convenient combinators (introduced by e.g. Curry, Rosser and others)*)
definition B'c::"('c \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'c \<Rightarrow> 'a" ("\<^bold>B''")
  where "\<^bold>B' \<equiv> \<lambda>f g x. g (f x)" (*reversed \<^bold>B (= \<^bold>C \<^bold>B)*)
definition S'c::"('b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>S''")
  where "\<^bold>S' \<equiv> \<lambda>y f w. (f w) (y w)" (*reversed \<^bold>S (= \<^bold>C \<^bold>S)*)
definition Wc::"('b \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>W")
  where "\<^bold>W \<equiv> \<lambda>f x. (f x) x"
definition Jc::"('b \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'a" ("\<^bold>J")
  where "\<^bold>J \<equiv> \<lambda>f y v w. (f y) ((f w) v)"
definition Tc::"'b \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>T")
  where "\<^bold>T \<equiv> \<lambda>x y. y x"  (*reversed function application*)
definition Vc::"'b \<Rightarrow> 'c \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> 'a) \<Rightarrow> 'a" ("\<^bold>V")
  where "\<^bold>V \<equiv> \<lambda>x y z. (z x) y"

named_theorems combs
declare Ic_def[combs] Kc_def[combs] Cc_def[combs]
        Bc_def[combs] B'c_def[combs]
        Sc_def[combs] S'c_def[combs] Wc_def[combs]
        Jc_def[combs] Tc_def[combs] Vc_def[combs]

lemma comb1_simp: "\<^bold>B \<^bold>C \<^bold>K = \<^bold>B \<^bold>K" unfolding combs ..
lemma comb2_simp: "(\<^bold>B \<^bold>C) ((\<^bold>B \<^bold>C) x) = x" unfolding combs ..
lemma comb3_simp: "(\<^bold>B x) \<^bold>I = x" unfolding combs ..
lemma comb4_simp: "\<^bold>C (\<^bold>C x) = x" unfolding combs ..
(*...*)

(*We can show (via \<lambda>-conversion) that the combinators S and K can be used to define all others*)
lemma "\<^bold>B = \<^bold>S (\<^bold>K \<^bold>S) \<^bold>K" unfolding combs .. 
lemma "\<^bold>C = \<^bold>S (\<^bold>S (\<^bold>K (\<^bold>S (\<^bold>K \<^bold>S) \<^bold>K)) \<^bold>S) (\<^bold>K \<^bold>K)" unfolding combs ..
lemma "\<^bold>C = \<^bold>S (\<^bold>B \<^bold>B \<^bold>S) (\<^bold>K \<^bold>K)" unfolding combs ..
lemma "\<^bold>I = \<^bold>S \<^bold>K \<^bold>K" unfolding combs ..
lemma "\<^bold>W = \<^bold>S \<^bold>S (\<^bold>S \<^bold>K)" unfolding combs ..
lemma "\<^bold>I = \<^bold>W \<^bold>K" unfolding combs ..
lemma "\<^bold>T = \<^bold>S (\<^bold>K (\<^bold>S (\<^bold>S \<^bold>K \<^bold>K))) \<^bold>K"  unfolding combs ..
(*...*)

(*\<^bold>S can itself be defined in terms of other combinators*)
lemma "\<^bold>S = \<^bold>B (\<^bold>B (\<^bold>B \<^bold>W) \<^bold>C) (\<^bold>B \<^bold>B)" unfolding combs ..
lemma "\<^bold>S = \<^bold>B (\<^bold>B \<^bold>W)(\<^bold>B \<^bold>B \<^bold>C)" unfolding combs ..
(*...*)

end