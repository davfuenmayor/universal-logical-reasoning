(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory rels (* A basic theory of relations *)
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
  where "\<Inter>\<^sup>rS \<equiv> \<lambda>a. \<Inter>[(\<lambda>R. R a) S]"
definition bigunionR::"EOp\<^sub>N(Rel('a,'b))" ("\<Union>\<^sup>r") 
  where "\<Union>\<^sup>rS \<equiv> \<lambda>a. \<Union>[(\<lambda>R. R a) S]"

lemma bigunionR_simpdef: "\<Inter>\<^sup>rS = (\<lambda>a b. \<forall>R. S R \<rightarrow> R a b)" 
  unfolding set_defs fImage_def biginterR_def by metis
lemma biginterR_simpdef: "\<Union>\<^sup>rS = (\<lambda>a b. \<exists>R. S R \<and> R a b)" 
  unfolding set_defs fImage_def bigunionR_def by metis

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

lemma bigdistrR1: "(R \<inter>\<^sup>r \<Union>\<^sup>rS) = \<Union>\<^sup>r[(\<lambda>X. R \<inter>\<^sup>r X) S]" 
  unfolding func_defs set_defs bigunionR_def by fastforce 
lemma bigdistrR2: "(R \<union>\<^sup>r \<Inter>\<^sup>rS) = \<Inter>\<^sup>r[(\<lambda>X. R \<union>\<^sup>r X) S]"
  unfolding func_defs set_defs biginterR_def by fastforce
lemma bigdeMorganR1: "\<midarrow>\<^sup>r(\<Union>\<^sup>rS) = \<Inter>\<^sup>r[\<midarrow>\<^sup>r S]" 
  unfolding func_defs set_defs bigunionR_def biginterR_def by fastforce
lemma bigdeMorganR2: "\<midarrow>\<^sup>r(\<Inter>\<^sup>rS) = \<Union>\<^sup>r[\<midarrow>\<^sup>r S]" 
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
definition rcomp::"('b,'c)Rel \<Rightarrow> ('a,'b)Rel \<Rightarrow> ('a,'c)Rel" (infixl "\<circ>\<^sup>r" 75)
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
definition rRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "rRange R \<equiv> \<lambda>b. \<exists>((R)\<^sup>T b)"

(*We can extend the definitions of the set-operators "image" and "preimage" for relations too.
  Read "rImage R A" as "the (relational) image of A under R".*)
definition rImage::"Rel('a,'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "rImage R \<equiv> \<lambda>A. \<lambda>b. \<exists>a. R a b \<and> A a"

(*Analogously, we define the "preimage" (aka. "inverse-image") set-operator corresponding to a relation.
  Read "rPreimage R B" as "the (relational) preimage of B under R".*)
definition rPreimage::"Rel('a,'b) \<Rightarrow> Set('b) \<Rightarrow> Set('a)"
  where "rPreimage \<equiv> \<lambda>R. \<lambda>B. \<lambda>a. \<exists>b. R a b \<and> B b"

declare rRange_def[rel_defs] rImage_def[rel_defs] rPreimage_def[rel_defs]


subsection \<open>Properties of relations\<close>

(*The 'defined' elements in R's domain (aka. 'domain of definition') are those elements related 
  by R to at least one element (i.e. have a non-empty image under R) *)
abbreviation(input) defined::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "defined R \<equiv> \<lambda>a. \<exists>(R a)"

lemma "defined R = rRange (R)\<^sup>T" unfolding rel_defs combs ..

(*A relation R is called 'total' (aka. 'serial' for endorelations) when it is defined for all elements
 in its domain. This definition can also be restricted to a subset A of R's domain. *)
definition totalRel::"Set(Rel('a,'b))"
  where \<open>totalRel R \<equiv> \<forall>(defined R)\<close>
definition totalRel_restr::"Set('a) \<Rightarrow> Set(Rel('a,'b))" ("totalRel[_]")
  where \<open>totalRel[A] R \<equiv> A \<subseteq> defined R\<close>

declare totalRel_def[rel_defs] totalRel_restr_def[rel_defs]

lemma totalRel_simp: "totalRel[\<UU>] R = totalRel R" unfolding rel_defs set_defs by simp

(*Analogous to functions, relations can be 'surjective' (wrt. subsets A/B of their domain/codomain)*)
definition surjectiveRel::"Set(Rel('a,'b))"
  where "surjectiveRel R \<equiv> \<forall>b. \<exists>a. R a b"
definition surjectiveRel_restr::"Set('a) \<Rightarrow> Set('b) \<Rightarrow>  Set(Rel('a,'b))" ("surjectiveRel[_,_]")
  where "surjectiveRel[A,B] R \<equiv> B \<subseteq> rImage R A"

declare surjectiveRel_def[rel_defs] surjectiveRel_restr_def[rel_defs]

lemma surjectiveRel_simp1: "surjectiveRel[\<UU>,\<UU>] R = surjectiveRel R" 
  unfolding rel_defs set_defs by simp
lemma surjectiveRel_simp2: \<open>surjectiveRel[\<UU>,B] R = totalRel[B] (R)\<^sup>T\<close> 
  unfolding rel_defs set_defs combs by simp

(*The 'determined' elements in R's domain are those for which R 'behaves deterministically', that is
 determined elements are related/mapped by R to at most one element. *)
abbreviation(input) determined::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "determined R \<equiv> \<lambda>a. \<exists>\<^sub>\<le>\<^sub>1(R a)"

(*A relation R is called 'deterministic' or 'partially-functional' wrt (a subset A of) its domain 
 when R behaves deterministically everywhere in (the subset A of) its domain. *)
definition deterministicRel::"Set(Rel('a,'b))"
  where \<open>deterministicRel R \<equiv> \<forall>(determined R)\<close>
definition deterministicRel_restr::"Set('a) \<Rightarrow> Set(Rel('a,'b))" ("deterministicRel[_]")
  where \<open>deterministicRel[A] R \<equiv> A \<subseteq> determined R\<close>

declare deterministicRel_def[rel_defs] deterministicRel_restr_def[rel_defs]


(*Analogous to functions, relations can be 'injective' (wrt. subsets A/B of their domain/codomain)*)
definition injectiveRel::"Set(Rel('a,'b))"
  where "injectiveRel R \<equiv> \<forall>b. \<exists>\<^sub>\<le>\<^sub>1a. R a b"
definition injectiveRel_restr::"Set('a) \<Rightarrow> Set('b) \<Rightarrow>  Set(Rel('a,'b))" ("injectiveRel[_,_]")
  where "injectiveRel[A,B] R \<equiv> \<forall>b. B b \<rightarrow> \<exists>\<^sub>\<le>\<^sub>1(A \<inter> (R)\<^sup>T b)"

declare injectiveRel_def[rel_defs] injectiveRel_restr_def[rel_defs]

lemma injectiveRel_simp1: "injectiveRel[\<UU>,\<UU>] R = injectiveRel R" 
  unfolding rel_defs set_defs combs by (meson Uniq_def)
lemma injectiveRel_simp2: \<open>injectiveRel[\<UU>,B] R = deterministicRel[B] (R)\<^sup>T\<close> 
  unfolding rel_defs set_defs by simp



subsection \<open>From functions to relations (and viceversa)\<close>

(*The "inverse" of a function 'f' is the a relation that assigns to each object 'b' in f's codomain
  the set of 'a's in f's domain that 'f' maps to 'b' (i.e. 'b's preimage under 'f') *)
definition inverse::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('b,'a)" ("[_]\<inverse>")
  where "inverse f \<equiv> \<lambda>b. \<lambda>a. f a = b"

declare inverse_def[rel_defs]

(*The corresponding lifted relation is always injective and surjective*)
lemma "injectiveRel [f]\<inverse>" unfolding rel_defs by (simp add: Uniq_def)
lemma "surjectiveRel [f]\<inverse>" unfolding rel_defs by (simp add: Uniq_def)


(*The inverse in terms of combinators*)
lemma "inverse = \<^bold>C ((\<^bold>B \<^bold>B) (=))"  unfolding combs inverse_def by auto
lemma "inverse = \<^bold>B (\<^bold>B'(=)) \<^bold>B'" unfolding combs inverse_def by auto

(*The inverse in terms of preimage*)
lemma "[f {b}]\<inverse> = [f]\<inverse> b" unfolding rel_defs func_defs by auto

(*Several operations and predicates on functions can be expressed in terms of the inverse*)
lemma imageFun_def2: "fImage f = (\<lambda>A. (\<lambda>b. [f]\<inverse> b \<inter> A \<noteq> \<emptyset>))" 
  unfolding func_defs set_defs rel_defs by meson
lemma rangeFun_def2: "fRange f = (\<lambda>b. \<exists>([f]\<inverse> b))"
  unfolding func_defs rel_defs ..
lemma "surjectiveFun[\<UU>,B] f = totalRel[B] [f]\<inverse>"
  unfolding func_defs set_defs rel_defs by simp
lemma "surjectiveFun f = totalRel [f]\<inverse>"
  unfolding func_defs rel_defs ..
lemma "injectiveFun f = deterministicRel [f]\<inverse>"
  unfolding func_defs rel_defs set_defs by auto

(*The inverse of a function gets its name from the following property of injective functions:*)
lemma "injectiveFun f \<rightarrow> \<iota> \<circ> [f]\<inverse> \<circ> f = ID"
  unfolding func_defs rel_defs combs by (simp add: the_equality)

(*The previous property motivates introducing the notion of 'inverse function' of a (bijective) function.*)
abbreviation(input) inverseFunction::"('a \<Rightarrow> 'b) \<Rightarrow> ('b \<Rightarrow> 'a)" ("'(_')\<inverse>")
  where "(f)\<inverse> \<equiv> \<iota> \<circ> [f]\<inverse>" (*Beware: this definition is well-behaved for bijective functions only!*)


(*Every function can be lifted to a (special kind of) relation via the following definition*)
definition toRel::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" ("[_]\<^sup>R")
  where "[f]\<^sup>R \<equiv> \<lambda>a. {f a}"

declare toRel_def[rel_defs]

(*The corresponding lifted relation is always total and deterministic: *)
lemma "totalRel [f]\<^sup>R" unfolding rel_defs set_defs by simp
lemma "deterministicRel [f]\<^sup>R" unfolding rel_defs set_defs by simp

(*The two previous ways of lifting functions to relations are in fact closely related: *)
lemma \<open>[f]\<inverse> = ([f]\<^sup>R)\<^sup>T\<close>
  unfolding rel_defs combs ..


subsection \<open>Relations to functions\<close>

(*A relation that is both deterministic and total relates each object in its domain to an unique
  object in its codomain, and thus gives rise to a function. We call such relations 'functional'.*)
definition functionalRel::"Set(Rel('a,'b))"
  where "functionalRel R \<equiv> totalRel R \<and> deterministicRel R"

declare functionalRel_def[rel_defs]

lemma functionalRel_def2: \<open>functionalRel R = (\<forall>a. \<exists>\<^sub>1(R a))\<close> 
  unfolding rel_defs set_defs combs by blast

(*Similarly, every functional (total and deterministic) relation can be converted into a function*)
definition toFun::"Rel('a,'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("[_]\<^sub>f")
  where "[R]\<^sub>f \<equiv> \<lambda>a. \<iota> b. R a b"

declare toFun_def[rel_defs]

(*This gives rise to useful simplification rules:*)
lemma funrel_simp1: "[[f]\<^sup>R]\<^sub>f = f" 
  unfolding rel_defs by simp 
lemma funrel_simp2: "functionalRel R \<Longrightarrow> [[R]\<^sub>f]\<^sup>R = R" 
  unfolding rel_defs set_defs apply (rule ext)+ by (metis theI)

declare funrel_simp1[rel_simps] funrel_simp2[rel_simps]


(*In fact, several notions for functions can be naturally stated in terms of relations, such as
  range, injectivity and surjectivity *)
lemma \<open>fRange f = rRange [f]\<^sup>R\<close>
  unfolding rel_defs func_defs combs ..
lemma \<open>injectiveFun f = injectiveRel [f]\<^sup>R\<close> 
  unfolding rel_defs func_defs using Uniq_def by auto
lemma \<open>surjectiveFun f = surjectiveRel [f]\<^sup>R\<close> 
  unfolding rel_defs func_defs by metis
lemma "injectiveFun[A] f = injectiveRel[A,\<UU>] [f]\<^sup>R"
  unfolding rel_defs func_defs set_defs combs by auto
lemma "surjectiveFun[A,B] f = surjectiveRel[A,B] [f]\<^sup>R" 
  unfolding rel_defs func_defs set_defs by auto

(*Moreover, the monoidal structure is preserved when passing from functions to relations and viceversa.
  This gives rise to useful simplification rules: *)
lemma ID_simp1: "[ID]\<^sup>R = ID\<^sup>r" 
  unfolding rel_defs combs by auto
lemma ID_simp2: "[ID\<^sup>r]\<^sub>f = ID" 
  unfolding rel_defs combs by simp
lemma comp_simp1: "[[f]\<^sup>R \<circ>\<^sup>r [g]\<^sup>R]\<^sub>f = (f \<circ> g)" 
  unfolding rel_defs combs by simp
lemma comp_simp2: "functionalRel R \<and> functionalRel T \<Longrightarrow> [[R]\<^sub>f \<circ> [T]\<^sub>f]\<^sup>R = (R \<circ>\<^sup>r T)"
  unfolding rel_defs combs by (metis (mono_tags, opaque_lifting) the_equality unique_def)

declare ID_simp1[rel_simps] ID_simp2[rel_simps] comp_simp1[rel_simps] comp_simp2[rel_simps]

end
