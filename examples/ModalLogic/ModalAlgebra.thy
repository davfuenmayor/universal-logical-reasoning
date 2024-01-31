(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory ModalAlgebra (* A theory of modal algebra(s) *)
  imports "../../library/sets" "../../library/endorels"
begin

(*Modal algebras extend (boolean) algebras of sets by adding an indexed collection of unary set-operations (modalities).
 Thus, the elements of modal algebras are sets (i.e. subsets of the universe \<UU>). Abusing mathematical jargon,
 we say that modal algebras are operation-extensions of the powerset lattice \<P>(\<UU>) (which is a boolean algebra).*)

(*So the following expressions are well-formed and denote elements of the algebra \<P>(\<UU>)*)
term "\<UU>" (*largest element of \<P>(\<UU>)*)
term "X \<union> Y"  (* 'join' operation in \<P>(\<UU>) *)
term "X \<inter> Y"  (* 'meet' operation in \<P>(\<UU>) *)
term "\<midarrow>X"     (* 'complement' operation in \<P>(\<UU>) *)
term "X \<subseteq> Y"  (* standard ordering in \<P>(\<UU>) *)

(*The previous definitions are generic, since they work for any (polymorphic) type 'a. 
 In order to introduce the indexed collection of operations (modalities), it is convenient to work 
 with a concrete (non-polymorphic) type 'w' (of 'worlds', 'states', 'situations', etc.). *)
typedecl w

(*We introduce 'i-indexed collections of (curried) endorelations on 'w' to encode (multi)modal frames.
 The type variable 'i corresponds to 'indexes' (or 'labels', 'agents', 'contexts', 'influences', etc.)*)
consts iR::"'i-Index(ERel(w))" (* 'i \<Rightarrow> ERel(w) *)

(*that is*)
term "iR::'i \<Rightarrow> (w \<Rightarrow> w \<Rightarrow> o)" 

(******* Syntactic-sugar configuration (feel free to ignore the details) *******) 
(* We introduce notation for writing "\<R>\<^sup>i" instead of "(iR i)" *)
notation iR ("\<R>\<^sup>_")
(* Introduce notation for writing "w \<rhd>\<^sup>i v" resp. "v \<lhd>\<^sup>i w" instead of "\<R>\<^sup>i w v" *)
syntax "iR_infix1"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic" ("_ \<lhd>\<^sup>_ _")
translations "a \<lhd>\<^sup>i b" == "CONST iR i b a"
syntax "iR_infix2"::"any \<Rightarrow> any \<Rightarrow> any \<Rightarrow> logic" ("_ \<rhd>\<^sup>_ _")
translations "a \<rhd>\<^sup>i b" == "CONST iR i a b"

(*Sanity check: notation is correctly configured*)
lemma "(iR i) a b = \<R>\<^sup>i a b" .. 
lemma "\<R>\<^sup>i a b = (a \<rhd>\<^sup>i b)" .. (*in Popkorn's book:  a \<longrightarrow>\<^sup>i b*)
lemma "(a \<rhd>\<^sup>i b) = (b \<lhd>\<^sup>i a)" .. (*in Popkorn's book: b \<prec>\<^sub>i a*)
(*******************************************************************************)
 
(*We now introduce our indexed family of modalities (as endo-operations) via the following definitions*)
definition iBox::"'i-Index(EOp(Set(w)))" ("[_]") (*type: 'i \<Rightarrow> (Set(w) \<Rightarrow> Set(w))*)
  where "[i]A \<equiv> \<lambda>w. \<forall>v. w \<rhd>\<^sup>i v \<rightarrow> A v"
definition iDia::"'i-Index(EOp(Set(w)))" ("<_>") (*type: 'i \<Rightarrow> (Set(w) \<Rightarrow> Set(w))*)
  where "<i>A \<equiv> \<lambda>w. \<exists>v. w \<rhd>\<^sup>i v \<and> A v"

(*So the following expressions are well-formed and denote elements of the modal algebra \<M>(\<UU>)*)
term "[i](A \<union> B)"
term "<i>(A \<inter> [i]B)"
term "<i>([i]B) \<union> \<midarrow>(<i>A)"

(*Duality between box and diamond modalities is easily provable*)
lemma "[i]A = \<midarrow>(<i>(\<midarrow>A))" 
  unfolding iBox_def iDia_def set_defs by simp


(*Transforming between modal operators back to relations*)
abbreviation getRelBackFromBox::"EOp(Set(w)) \<Rightarrow> ERel(w)"
  where "getRelBackFromBox op \<equiv> \<lambda>a b. \<forall>X. (op X) a \<rightarrow> X b"

lemma "getRelBackFromBox [i] a b = a \<rhd>\<^sup>i b" 
  by (metis iBox_def)

(*Exercise: define "getRelBackFromDiamond" *)


(*Modal correspondences (between properties of relations and their respective box/diamond modalities) *)

(*Properties of unary operations on sets (aka modalities)*)
abbreviation "Inflationary op \<equiv> \<forall>A.  A \<subseteq> (op A)"
abbreviation "Deflationary op \<equiv> \<forall>A. (op A) \<subseteq> A"
abbreviation "NearlyInflationary op \<equiv> \<forall>A. (op A) \<subseteq> op (op A)"
abbreviation "NearlyDeflationary op \<equiv> \<forall>A. op (op A) \<subseteq> (op A)"
(*...*)

(*Properties of unary set-operations correspond to properties of relations*)
lemma reflexive_corr: "Deflationary [i] = reflexive \<R>\<^sup>i"  
  unfolding iBox_def Reflexive_def subset_def by auto
lemma coreflexive_corr: "Inflationary [i] = coreflexive \<R>\<^sup>i"
  unfolding iBox_def coreflexive_char by (smt (verit, ccfv_threshold) Coreflexive_def subset_def)
lemma transitive_corr: "NearlyInflationary [i] = transitive \<R>\<^sup>i"
  unfolding iBox_def transitive_char subset_def by auto 
lemma dense_corr: "NearlyDeflationary [i] = dense \<R>\<^sup>i"
  sorry (*TODO: reconstruction in kernel fails - fix*)

(* Exercise: encode more correspondences ...*)

end