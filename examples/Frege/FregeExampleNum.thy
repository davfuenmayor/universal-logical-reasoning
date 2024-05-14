(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory FregeExampleNum (* Frege - Foundations of Arithmetic \<section>62-69  (part III) *)
imports "../../library/pairs" "../../library/endorels"
begin

(*We can provide a definition for "equinumerosity" of sets, following so-called "Hume's Principle".
 It says, informally, that the number of As is equal to the number of Bs iff there is a one-to-one 
 correspondence (a bijection) between the As and the Bs*)
definition equinumerous::"Rel(Set('a),Set('b))" (infix "\<approx>" 99) (* Set('a) \<Rightarrow> (Set('a) \<Rightarrow> bool) *)
  where "A \<approx> B \<equiv> \<exists>f. bijectiveMap[A,B] f"

lemma REFL: "reflexive (\<approx>)" 
  unfolding equinumerous_def Reflexive_def func_defs by fastforce
lemma SYMM: "symmetric (\<approx>)"  
  unfolding equinumerous_def Symmetric_def func_defs (*by metis*) sorry (*kernel reconstruction fails*)
lemma TRAN: "transitive (\<approx>)" 
  by (smt (z3) bijectiveMap_def injectiveMap_comp equinumerous_def surjectiveMap_comp surjectiveMap_simpdef transitive_char)

(*or, in other words *)
lemma "equivalence (\<approx>)" unfolding equivalence_def using REFL SYMM TRAN by auto

(*Now recall that relations are also set-valued functions, so the following statement is well-formed *)
term "(\<approx>) a" (* i.e. (\<lambda>x. a \<approx> x) set of sets equinumerous to a*)

(*Frege (and later Russell-Whitehead) defines the 'number' (cardinality) of a concept (set) as the 
 set formed by all sets equinumerous to it. That is, cardinalities are defined as equivalence classes.*)
definition cardinality::"Set('a) \<Rightarrow> Set(Set('a))" ("|_|") (*cf. Frege and Russel & Whitehead ("non-representational", Hallett 1984 "Cantorian set theory and limitation of size")*)
  where "|a| \<equiv> \<lambda>x. a \<approx> x " (*i.e. (\<approx>) a *) (*TODO: tools have different behaviour*)

(*The "cardinality" function assigns to a given set its cardinality (the set of sets equinumerous to it) *)
term "cardinality::Set('a) \<Rightarrow> Set(Set('a))"
term "cardinality::ERel(Set('a))"
term "cardinality A" (*the cardinality of set A *)

(*but now note that (by eta-reduction)*)
lemma "cardinality = equinumerous" unfolding cardinality_def ..

(*The main statement: two sets are equinumerous iff they have the same cardinality*)
lemma main: "A \<approx> B = ( |A| = |B| )" 
  unfolding cardinality_def by (metis REFL Reflexive_def SYMM Symmetric_def TRAN Transitive_def)


section \<open>Comparing set sizes\<close>

(*Injective account of set 'size':
B is at least as big as A iff any two distinct members of A can be paired with distinct members of B.
A is at least as small as B when there is an injection from A into B *)
definition size_order::"Rel(Set('a),Set('b))" (infix "\<preceq>" 99)
  where "A \<preceq> B \<equiv> \<exists>f. injectiveMap[A,B] f"

(*Surjective account of set 'size': 
B is at least as big as A if and only if any two distinct members of A can be paired with disjoint parts of B.
A is at least as small as B just in case there is a surjection from B onto A (or A is empty) *)
lemma "A \<preceq> B = (\<exists>A \<longrightarrow> (\<exists>f. surjectiveMap[B,A] f))"
  by (metis (mono_tags, lifting) inj_to_surj_map surj_to_inj_map injectiveFun_restr_def map_def size_order_def)

lemma size_order_refl: "reflexive (\<preceq>)" by (metis Reflexive_def size_order_def bijectiveMap_def equinumerous_def main surjectiveMap_simpdef) 
lemma size_order_trans: "transitive (\<preceq>)"  unfolding Transitive_def size_order_def using injectiveMap_comp by blast
lemma "antisymmetric (\<preceq>)" nitpick oops (*counterexample: size ordering is not antisymmetric *)

(*The symmetric part of the size ordering corresponds to equinumerosity (aka. Cantor-Schroeder-Bernstein theorem)*)
theorem CSB: "A \<approx> B = (A \<preceq> B \<and> B \<preceq> A)" 
  by (meson bijectiveMap_def equinumerous_def inj_to_bij_map surj_to_inj_map surjectiveMap_simpdef size_order_def)


section \<open>Towards "cardinal numbers"\<close>

(*We saw previously that equinumerosity corresponds to the identity of cardinalities: *)
lemma "A \<approx> B \<longleftrightarrow> |A| = |B|" by (simp add: main)
(* However, the analogous result does not hold for size orderings*)
lemma "A \<preceq> B \<longleftrightarrow> |A| \<preceq> |B|" nitpick oops
(*Moreover, sets are not even equinumerous to their cardinalities (which are typically much larger in size)*)
lemma "|x| \<approx> x" nitpick oops

(*These discrepancies motivate the following definition of a cardinal (number); cf. Zermelo and von Neumann *)
abbreviation(input) cardinal::"Set('a) \<Rightarrow> Set('a)" ("|_|\<^sup>#")
  where "|a|\<^sup># \<equiv> \<epsilon>|a|"

(*The previous definition validates in fact the desired properties: *)
lemma "A \<approx> B \<longleftrightarrow> |A|\<^sup># = |B|\<^sup>#" using main by (metis cardinality_def some_eq_imp)
lemma "A \<preceq> B \<longleftrightarrow> |A|\<^sup># \<preceq> |B|\<^sup>#" oops (*TODO: prove*)
lemma "|x|\<^sup># \<approx> x" by (metis cardinality_def main someI)

(*The set of all cardinal numbers is in fact definable as the range of the "cardinal" function*)
term "fRange cardinal" 
  
(***Advanced: encoding cardinal arithmetic***)
(*See: https://ncatlab.org/nlab/show/cardinal+arithmetic *)

end