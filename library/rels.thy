(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory rels (* A basic theory of relations (qua set-valued functions) *)
imports sets
begin

section \<open>Relations\<close>

(*Let's put relation-related definitions/simplification-rules in two bags ("rel_defs" resp. "rel_simps") *)
named_theorems rel_defs
named_theorems rel_simps


subsection \<open>Basic Predicates\<close>

(*Analogously to sets, we define that a given relation holds of all, resp. at least one, pair or elements.*)
abbreviation(input) AllR::"Set(Rel('a,'b))" ("\<forall>\<^sup>r") 
  where "\<forall>\<^sup>r R \<equiv> \<forall>a b. R a b"
abbreviation(input)  ExR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r")
  where "\<exists>\<^sup>r R \<equiv> \<exists>a b. R a b"

(* "\<exists>\<^sup>r\<^sub>\<le>\<^sub>1 R" means: R holds of at most one pair of elements (R may hold of none)*)
definition uniqueR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r\<^sub>\<le>\<^sub>1")
  where \<open>\<exists>\<^sup>r\<^sub>\<le>\<^sub>1 R \<equiv> \<forall>a b x y. (R a b \<and> R x y) \<rightarrow> (a = x \<and> b = y)\<close>

(* "\<exists>\<^sup>r\<^sub>1 R" means: R holds of exactly one pair of elements, i.e. R is a 'singleton relation'. *)
definition singleR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r\<^sub>1")
  where \<open>\<exists>\<^sup>r\<^sub>1 R \<equiv> \<exists>x y. R x y \<and> (\<forall>a b. R a b \<rightarrow> (a = x \<and> b = y))\<close>

declare uniqueR_def[rel_defs] singleR_def[rel_defs]

lemma singleR_def2: "\<exists>\<^sup>r\<^sub>1 R = (\<exists>\<^sup>r R \<and> \<exists>\<^sup>r\<^sub>\<le>\<^sub>1 R)"
  unfolding singleR_def uniqueR_def by blast


subsection \<open>Algebraic structure\<close>

subsubsection \<open>Boolean structure\<close>
(*As we have seen, (curried) relations correspond to indexed families of sets. 
  It is thus not surprising that they inherit their Boolean algebra structure.*)

(*The "universal" and the "empty" relation can be seen as 0-ary operations on relations.*)
abbreviation univR::"Rel('a,'b)" ("\<UU>\<^sup>r")
  where "\<UU>\<^sup>r \<equiv> \<lambda>a. \<UU>"
abbreviation emptyR::"Rel('a,'b)" ("\<emptyset>\<^sup>r")
  where "\<emptyset>\<^sup>r \<equiv> \<lambda>a. \<emptyset>"

(*The complement of a relation is a unary operation. It gets a special prefix-superscript notation.*)
abbreviation (input) complR::"EOp(Rel('a,'b))" ("\<midarrow>\<^sup>r") 
  where \<open>\<midarrow>\<^sup>rR \<equiv> \<lambda>a. \<midarrow>(R a)\<close>

notation (input) complR ("'(_')\<^sup>-") (* alternative notation common in the literature *)

(*We can also define some binary operations on relations *)
abbreviation interR::"EOp\<^sub>2(Rel('a,'b))" (infixr "\<inter>\<^sup>r" 54) 
  where "R \<inter>\<^sup>r T \<equiv> \<lambda>a. R a \<inter> T a"
abbreviation unionR::"EOp\<^sub>2(Rel('a,'b))" (infixr "\<union>\<^sup>r" 53) 
  where "R \<union>\<^sup>r T \<equiv> \<lambda>a. R a \<union> T a"
abbreviation diffR:: "EOp\<^sub>2(Rel('a,'b))" (infixr "\<leftharpoonup>\<^sup>r" 51) 
  where "R \<leftharpoonup>\<^sup>r T \<equiv> \<lambda>a. R a \<leftharpoonup> T a" (** relation-difference*)

(*We can also generalize union and intersection to the infinitary case*)
definition biginterR::"EOp\<^sub>N(Rel('a,'b))" ("\<Inter>\<^sup>r") 
  where "\<Inter>\<^sup>rS \<equiv> \<lambda>a. \<Inter>\<lbrakk>(\<lambda>R. R a) S\<rbrakk>"
definition bigunionR::"EOp\<^sub>N(Rel('a,'b))" ("\<Union>\<^sup>r") 
  where "\<Union>\<^sup>rS \<equiv> \<lambda>a. \<Union>\<lbrakk>(\<lambda>R. R a) S\<rbrakk>"

lemma biginterR_simpdef: "\<Inter>\<^sup>rS = (\<lambda>a b. \<forall>R. S R \<rightarrow> R a b)" 
  unfolding set_defs funImage_def biginterR_def by metis
lemma bigunionR_simpdef: "\<Union>\<^sup>rS = (\<lambda>a b. \<exists>R. S R \<and> R a b)" 
  unfolding set_defs funImage_def bigunionR_def by metis

(*The definitions above are intuitive when seeing relations as binary predicates: *)
lemma "\<UU>\<^sup>r = (\<lambda>a b. True)" ..
lemma "\<emptyset>\<^sup>r = (\<lambda>a b. False)" ..
lemma "\<midarrow>\<^sup>rR = (\<lambda>a b. \<not>R a b)" unfolding set_defs ..
lemma "R \<inter>\<^sup>r T  = (\<lambda>a b. R a b \<and> T a b)" unfolding set_defs ..
lemma "R \<union>\<^sup>r T  = (\<lambda>a b. R a b \<or> T a b)" unfolding  set_defs ..
lemma "R \<leftharpoonup>\<^sup>r T = (\<lambda>a b. R a b  \<and> \<not>T a b)" unfolding  set_defs ..

lemma "R \<inter>\<^sup>r (T \<union>\<^sup>r U) = ((R \<inter>\<^sup>r T) \<union>\<^sup>r (R \<inter>\<^sup>r U))" unfolding distr1 .. 
lemma "R \<union>\<^sup>r (T \<inter>\<^sup>r U) = ((R \<union>\<^sup>r T) \<inter>\<^sup>r (R \<union>\<^sup>r U))" unfolding distr2 .. 
lemma "\<midarrow>\<^sup>r(R \<union>\<^sup>r T) = (\<midarrow>\<^sup>rR \<inter>\<^sup>r \<midarrow>\<^sup>rT)" unfolding deMorgan1 ..
lemma "\<midarrow>\<^sup>r(R \<inter>\<^sup>r T) = (\<midarrow>\<^sup>rR \<union>\<^sup>r \<midarrow>\<^sup>rT)" unfolding deMorgan2 ..

lemma bigdistrR1: "(R \<inter>\<^sup>r \<Union>\<^sup>rS) = \<Union>\<^sup>r\<lbrakk>(\<lambda>X. R \<inter>\<^sup>r X) S\<rbrakk>" 
  unfolding func_defs set_defs bigunionR_def by fastforce 
lemma bigdistrR2: "(R \<union>\<^sup>r \<Inter>\<^sup>rS) = \<Inter>\<^sup>r\<lbrakk>(\<lambda>X. R \<union>\<^sup>r X) S\<rbrakk>"
  unfolding func_defs set_defs biginterR_def by fastforce
lemma bigdeMorganR1: "\<midarrow>\<^sup>r(\<Union>\<^sup>rS) = \<Inter>\<^sup>r\<lbrakk>\<midarrow>\<^sup>r S\<rbrakk>" 
  unfolding func_defs set_defs bigunionR_def biginterR_def by fastforce
lemma bigdeMorganR2: "\<midarrow>\<^sup>r(\<Inter>\<^sup>rS) = \<Union>\<^sup>r\<lbrakk>\<midarrow>\<^sup>r S\<rbrakk>" 
  unfolding func_defs set_defs bigunionR_def biginterR_def by fastforce

lemma deMorganQR1: "(\<not>\<exists>\<^sup>r(\<midarrow>\<^sup>rA)) = \<forall>\<^sup>rA" unfolding compl_def by simp
lemma deMorganQR2: "(\<not>\<forall>\<^sup>r(\<midarrow>\<^sup>rA)) = \<exists>\<^sup>rA" unfolding compl_def by simp


subsubsection \<open>Ordering structure\<close>
(*Similarly, relations also inherit the ordering structure of sets.*)

abbreviation subrel::"ERel(Rel('a,'b))" (infixr "\<subseteq>\<^sup>r" 51) 
  where "R \<subseteq>\<^sup>r T \<equiv> \<forall>a. R a \<subseteq> T a"

abbreviation(input) superrel::"ERel(Rel('a,'b))" (infixr "\<supseteq>\<^sup>r" 51)
  where "A \<supseteq>\<^sup>r B \<equiv> B \<subseteq>\<^sup>r A" (*for convenience*)

abbreviation(input) psubrel::"ERel(Rel('a,'b))" (infixr "\<subset>\<^sup>r" 51) (*proper subrelation*)
  where "A \<subset>\<^sup>r B \<equiv> A \<subseteq>\<^sup>r B \<and> \<exists>\<^sup>r(B \<leftharpoonup>\<^sup>r A)"
abbreviation(input) psuperset::"ERel(Rel('a,'b))" (infixr "\<supset>\<^sup>r" 51) (*proper superrelation*)
  where "A \<supset>\<^sup>r B \<equiv> B \<subset>\<^sup>r A" (*for convenience*)


subsubsection \<open>Ring structure\<close>
(*We have seen the shared (boolean) algebraic structure between sets and relations. 
 We now explore their shared (monoidal) algebraic structure with functions.*)

(*Analogously to functions, relations can also be composed.*)
definition rcomp::"Rel('b,'c) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('a,'c)" (infixl "\<circ>\<^sup>r" 75)
  where "T \<circ>\<^sup>r R \<equiv> \<lambda>a c. \<exists>b. R a b \<and> T b c"

declare rcomp_def[rel_defs]

(*In fact, equalities play the role of identity elements (one identity for each type)*)
notation(input) HOL.eq ("ID\<^sup>r")

(*Thus we have*)
lemma "ID\<^sup>r = (=)" .. 
lemma "ID\<^sup>r a b = (a = b)" .. 

(*Relation composition and identity satisfy the monoid conditions*)
lemma rcomp_assoc: "(R \<circ>\<^sup>r T) \<circ>\<^sup>r V = R \<circ>\<^sup>r (T \<circ>\<^sup>r V)" unfolding rcomp_def by auto (* associativity *)
lemma rcomp_idl: "ID\<^sup>r \<circ>\<^sup>r R = R" unfolding rcomp_def by simp                   (* left identity *)
lemma rcomp_idr: "R \<circ>\<^sup>r ID\<^sup>r = R" unfolding rcomp_def by simp                   (* right identity *)


subsection \<open>Restriction\<close>

(*(Cartesian) product and (disjoint) sum/union*)
abbreviation(input) product::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<times>" 90)
  where "A \<times> B \<equiv> \<lambda>x y. A x \<and> B y"
abbreviation(input) sum::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<uplus>" 90)
  where "A \<uplus> B \<equiv> \<lambda>x y. A x \<or> B y"

(*Restricting the domain of a relation to a subset A*)
abbreviation(input) restrDom::"Set('a) \<Rightarrow> EOp(Rel('a,'b))" ("_\<downharpoonleft>") 
  where \<open>A\<downharpoonleft>R \<equiv> \<lambda>a b. A a \<and> R a b\<close>

(*Restricting the codomain of a relation to a subset B*)
abbreviation(input) restrCod::"Set('b) \<Rightarrow> EOp(Rel('a,'b))" ("_\<downharpoonright>") 
  where \<open>B\<downharpoonright>R \<equiv> \<lambda>a b. B b \<and> R a b\<close>

(*Restricting both domain and codomain of a relation wrt. the given subsets A and B*)
abbreviation(input) restrBoth::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> EOp(Rel('a,'b))" ("'(_,_')\<down>"[99]) 
  where \<open>(A,B)\<down>R \<equiv> \<lambda>a b. A a \<and> B b \<and> R a b\<close>

lemma "A\<downharpoonleft>R = (A \<times> \<UU>) \<inter>\<^sup>r R" unfolding inter_def by simp
lemma "B\<downharpoonright>R = (\<UU> \<times> B) \<inter>\<^sup>r R" unfolding inter_def by simp
lemma "(A,B)\<down>R = ((A \<times> B) \<inter>\<^sup>r R)" unfolding inter_def by simp

lemma "(S\<downharpoonleft>R) = (S\<downharpoonright>((R)\<^sup>T))\<^sup>T" unfolding combs ..

lemma "D\<downharpoonleft>(C\<downharpoonright>R) = (D,C)\<down>R" ..
lemma "C\<downharpoonright>(D\<downharpoonleft>R) = (D,C)\<down>R" by blast

lemma "\<UU>\<downharpoonleft>R = R" by simp
lemma "\<UU>\<downharpoonright>R = R" by simp
lemma "(\<UU>,\<UU>)\<down>R = R" by simp


subsection \<open>Range, Image & preimage of relations\<close>

(*Given a relation R we can obtain its (relational) range as the set of those objects in the codomain
  that have a non-empty preimage (they are the image of some object).*)
definition relRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "relRange R \<equiv> \<lambda>b. \<exists>((R)\<^sup>T b)"

(*We can extend the definitions of the set-operators "image" and "preimage" for relations too.
  Read "relImage R A" as "the (relational) image of A under R".*)
definition relImage::"Rel('a,'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "relImage R \<equiv> \<lambda>A. \<lambda>b. \<exists>a. R a b \<and> A a"

(*Analogously, we define the "preimage" (aka. "inverse-image") set-operator corresponding to a relation.
  Read "relPreimage R B" as "the (relational) preimage of B under R".*)
definition relPreimage::"Rel('a,'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)"
  where "relPreimage R \<equiv> \<lambda>B. \<lambda>a. \<exists>b. R a b \<and> B b"

(*The notions of image and preimage of relations have in fact their 'dual' counterparts:*)
definition relDualImage::"Rel('a,'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "relDualImage R    \<equiv> \<lambda>A. \<lambda>b. \<forall>a. R a b \<longrightarrow> A a"
definition relDualPreimage::"Rel('a,'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)"
  where "relDualPreimage R \<equiv> \<lambda>B. \<lambda>a. \<forall>b. R a b \<longrightarrow> B b"

declare relRange_def[rel_defs] relImage_def[rel_defs] relPreimage_def[rel_defs]


(*Some miscelaneous characterizations*)
lemma "relImage R A = \<Union>(funImage R A)" 
  unfolding relImage_def funImage_def bigunion_def by metis


subsection \<open>Inverting functions\<close>

(*The "inverse" of a function 'f' is the a relation that assigns to each object 'b' in f's codomain
  the set of 'a's in f's domain that 'f' maps to 'b' (i.e. 'b's preimage under 'f') *)
definition inverse::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('b,'a)" ("[_]\<inverse>")
  where "inverse f \<equiv> \<lambda>b. \<lambda>a. f a = b"

declare inverse_def[rel_defs]

(*The inverse in terms of combinators*)
lemma "inverse = \<^bold>C ((\<^bold>B \<^bold>B) (=))"  unfolding combs inverse_def by auto
lemma "inverse = \<^bold>B (\<^bold>B'(=)) \<^bold>B'" unfolding combs inverse_def by auto

(*The inverse in terms of preimage*)
lemma "\<lbrakk>f {b}\<rbrakk>\<inverse> = [f]\<inverse> b" unfolding rel_defs func_defs by auto

(*Several operations and predicates on functions can be expressed in terms of the inverse*)
lemma imageFun_def2: "funImage f = (\<lambda>A. (\<lambda>b. [f]\<inverse> b \<inter> A \<noteq> \<emptyset>))" 
  unfolding func_defs set_defs rel_defs by meson
lemma rangeFun_def2: "funRange f = (\<lambda>b. \<exists>([f]\<inverse> b))"
  unfolding func_defs rel_defs ..

end
