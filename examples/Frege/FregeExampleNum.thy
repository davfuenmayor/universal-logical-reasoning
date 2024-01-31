(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory FregeExampleNum (* Frege - Foundations of Arithmetic \<section>62-69  (part III) *)
imports "../../library/pairs" "../../library/endorels"
begin

(*We can in fact provide a definition for "equinumerosity/equipollence"*)
definition equinumerous::"ERel(Set('a))" (infix "\<sim>\<^sup>n" 99) (* Set('a) \<Rightarrow> (Set('a) \<Rightarrow> bool) *)
  where "A \<sim>\<^sup>n B \<equiv> \<exists>f. bijectiveMap[A,B] f"

lemma REFL: "reflexive (\<sim>\<^sup>n)" 
  unfolding equinumerous_def Reflexive_def func_defs by fastforce
lemma SYMM: "symmetric (\<sim>\<^sup>n)"  
  unfolding equinumerous_def Symmetric_def func_defs sorry (*Exercise: prove*)
lemma TRAN: "transitive (\<sim>\<^sup>n)" 
  sorry (*Exercise: prove*)

(*or, in other words *)
lemma "equivalence (\<sim>\<^sup>n)" unfolding equivalence_def using REFL SYMM TRAN by auto

(*We have introduced a new term into the language (via definition)*)
term "(\<sim>\<^sup>n)"
term "(\<sim>\<^sup>n)::ERel(Set('a))"
term "(\<sim>\<^sup>n)::ERel*(Set('a))"  (*error: wrong type*)
term "(\<sim>\<^sup>n) \<langle>a,b\<rangle>" (*due to polymorphism this is in fact a well-formed formula (but not what you might think)*)
term "(\<sim>\<^sup>n) a b"

(*Some facts about equinumerousity follow from being an equivalence relation*)
lemma "a \<sim>\<^sup>n b \<and> \<not>(c \<sim>\<^sup>n b) \<longrightarrow> \<not>(a \<sim>\<^sup>n c)"
  by (metis SYMM Symmetric_def TRAN Transitive_def)

(*Now recall that relations are also set-valued functions, so the following statements is well-formed *)
term "(\<sim>\<^sup>n) a" (*set of sets equinumerous to a*)
term "equinumerous a" (*set of sets equinumerous to a*)

(*Frege defines the 'number' (cardinality) of a concept (set) as the set (equivalence class) of sets equinumerous to it *)
definition cardinality::"Set('a) \<Rightarrow> Set(Set('a))" ("|_|")
  where "|a| \<equiv> \<lambda>x. a \<sim>\<^sup>n x"

(*The "cardinality" function assigns to a given set its cardinal(ity) (the set of sets equinumerous to it) *)
term "cardinality"
term "cardinality::Set('a) \<Rightarrow> Set(Set('a))"
term "cardinality::ERel(Set('a))"
term "cardinality A" (*the cardinal(ity) of set A *)

(*but now note that (by eta-reduction)*)
lemma "cardinality = equinumerous" unfolding cardinality_def ..

(*The main statement: two sets are equinumerous iff they have the same cardinality*)
lemma main: "A \<sim>\<^sup>n B \<longleftrightarrow> cardinality A = cardinality B" 
  unfolding cardinality_def by (metis REFL Reflexive_def SYMM Symmetric_def TRAN Transitive_def)


section \<open>Towards "cardinal numbers"\<close>

(*(1) define is the set of all cardinal(itie)s *)
(*(2) define the natural ordering of cardinals *)
(*(3) define algebraic (arithmetic) operations on cardinals*)

(*The set of cardinal numbers is the range of the cardinality function (that assigns a cardinal to a set)*)
abbreviation "\<CC> \<equiv> fRange cardinality" 

(*We say that A is at least as small as B when there is an injection from A into B *)
definition atLeastAsSmallAs::"Rel(Set('a),Set('b))" (infix "\<preceq>" 99)
  where "A \<preceq> B \<equiv> (\<exists>f. mapping[A,B] f \<and> injectiveFun[A] f)"

lemma "reflexive (\<preceq>)" oops (*Exercise: prove*)
lemma "transitive (\<preceq>)" oops (*Exercise: prove*)
lemma "antisymmetric (\<preceq>)" nitpick oops (*counterexample: "at least as small as" is not antisymmetric! *)

(*The "at-least-as-small-as" relation can be used to provide a natural ordering for cardinals.
  This is a major theorem in set-theory, known as the Cantor-Schroeder-Bernstein theorem.*)
theorem CSB: "(A \<preceq> B \<and> B \<preceq> A) \<longrightarrow> A \<sim>\<^sup>n B" 
  oops (*Advanced exercise: prove *)


(***Advanced: encoding cardinal arithmetic***)
(*See: https://ncatlab.org/nlab/show/cardinal+arithmetic *)

end