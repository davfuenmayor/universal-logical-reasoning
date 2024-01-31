(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory description_logics
  imports "../../library/endorels"
begin


section \<open>Description Logic Experiments\<close>

subsection \<open>Encoding ALC (+ nominals and number restrictions)\<close>

abbreviation dl_conj (infixr "\<^bold>\<sqinter>" 71)
  where "A \<^bold>\<sqinter> B \<equiv> A \<inter> B"
abbreviation dl_disj (infixr "\<^bold>\<squnion>" 70)
  where "A \<^bold>\<squnion> B \<equiv> A \<union> B"
abbreviation dl_neg ("\<^bold>\<not>_" [73]74)
  where "\<^bold>\<not>A \<equiv> \<midarrow>A"

abbreviation dl_top ("\<^bold>\<top>")
  where "\<^bold>\<top> \<equiv> \<UU>"
abbreviation dl_bot ("\<^bold>\<bottom>")
  where "\<^bold>\<bottom> \<equiv> \<emptyset>"

(*Introduce convenient postfix-superscript notation for the complement (negation) of a relation (role).*)
notation (input) complR ("(_\<^sup>-)" [1000]1000)

abbreviation dl_ex ("\<^bold>\<exists>_\<sqdot>_")   (*notation warning: the thick dot is written: \sqdot *)
  where "\<^bold>\<exists>r\<sqdot>C \<equiv> rPreimage r C"
abbreviation dl_all ("\<^bold>\<forall>_\<sqdot>_")
  where "\<^bold>\<forall>r\<sqdot>C \<equiv> rDualPreimage r C"

(*(Qualified) number restrictions \<le>\<^sub>nr (\<le>\<^sub>nr.C) can also be introduced (see below for an example) *)

abbreviation dl_subs::"ERel(Set('i))" (infix "\<^bold>\<sqsubseteq>" 65) 
  where "A \<^bold>\<sqsubseteq> B \<equiv> A \<subseteq> B"

abbreviation dl_equiv::"ERel(Set('i))" (infix "\<^bold>\<equiv>" 65)
  where "A \<^bold>\<equiv> B \<equiv> A \<^bold>\<sqsubseteq> B \<and> B \<^bold>\<sqsubseteq> A"

(*Note that by extensionality:*)
lemma dl_equiv_char: "A \<^bold>\<equiv> B = (A = B)" unfolding subset_def by auto

abbreviation(input) con_inst::"'i \<Rightarrow> Set('i) \<Rightarrow> bool" (infix ":" 65)
  where "a : A \<equiv> A a"

abbreviation(input) rel_inst::"'i \<Rightarrow> 'i \<Rightarrow> ERel('i) \<Rightarrow> bool" ("\<lparr>_ , _\<rparr> : _")
  where "\<lparr>a, b\<rparr> : r \<equiv> r a b"


subsection \<open>Vocabulary\<close>

typedecl i (*type for individuals*)
type_synonym c = "Set(i)" (*type for concepts*)
type_synonym r = "ERel(i)" (*type for roles*)

(*Concept names*)
consts Person::c   Writer::c   Book::c        Novel::c
consts Poor::c     Famous::c   European::c    British::c

(*Role names*)
consts author::r      coauthor::r     bornIn::r      cityOf::r
consts parentOf::r    brotherOf::r    childOf::r     uncleOf::r

(*Individual names*)
consts Alice::i    Bob::i    GeorgeOrwell::i    AnimalFarm::i    Bihar::i    India::i


subsection \<open>Knowledge Base Example\<close>

(*TBox*)
axiomatization where
  T1: "Writer \<^bold>\<equiv> (Person \<^bold>\<sqinter> \<^bold>\<exists>author\<sqdot>Book)" and
  T2: "Novel \<^bold>\<sqsubseteq> Book"
(* .... *)

(*ABox*)
axiomatization where
  A1: "GeorgeOrwell : Person" and
  A2: "AnimalFarm : Novel" and
  A3: "\<lparr>GeorgeOrwell, AnimalFarm\<rparr> : author" and
  A4: "\<lparr>GeorgeOrwell, Bihar\<rparr> : bornIn" and
  A5: "\<lparr>Bihar, India\<rparr> : cityOf"
(* .... *)

(* GeorgeOrwell is a writer*)
lemma "GeorgeOrwell : Writer"
  by (metis (full_types) A1 A2 A3 T1 T2 inter_def rPreimage_def subset_def)

(* GeorgeOrwell is (supposed to be) European*)
lemma "GeorgeOrwell : European" nitpick oops (*countermodel found: background knowledge is missing *)

(*adds further background knowledge to TBox and ABox*)
axiomatization where
(* .... *)
  T3: "British \<^bold>\<sqsubseteq> European" and
(* .... *)
  A6: "GeorgeOrwell : British" (*is he?*)
(* .... *)

(*Now we get what we intended*)
lemma "GeorgeOrwell : European" (*is he?*)
  by (meson A6 T3 subset_def)



subsection \<open>Extended language\<close>


(*Nominals*)
lemma "x : \<^bold>\<exists>bornIn\<sqdot>{Bamberg} \<leftrightarrow> bornIn x Bamberg"
  by (simp add: rPreimage_def)
lemma "Anne : \<^bold>\<exists>bornIn\<sqdot>{Tokio, London, Bamberg} \<leftrightarrow> (bornIn Anne Tokio) \<or> (bornIn Anne London) \<or> (bornIn Anne Bamberg)"
  by (smt (verit) rPreimage_def)


(*Role composition*)
abbreviation dl_role_comp::"ERel('i) \<Rightarrow> ERel('i) \<Rightarrow> ERel('i)" (infixr "\<sqdot>" 90)
  where "r\<^sub>1 \<sqdot> r\<^sub>2 \<equiv> r\<^sub>2 \<circ>\<^sup>r r\<^sub>1"

(*Range restriction (for roles)*)
abbreviation range_restr::"ERel('i) \<Rightarrow> Set('i) \<Rightarrow> ERel('i)" ("_|_")
  where "R|C \<equiv> C\<downharpoonright>R"

(*useful derived definition (cf. dynamic logic)*)
definition test::"Set('i) \<Rightarrow> ERel('i)" ("_?")
  where "P? \<equiv> (=)|P"

(*Both notions are interrelated*)
lemma "R|C = (R \<sqdot> C?)"
  unfolding rcomp_def test_def by auto


(*An example:*)
consts consumes::r
consts Drink::c
definition drinks::r
  where "drinks x d \<equiv> consumes x d \<and> Drink d"

lemma "drinks = (consumes|Drink)"
  unfolding rcomp_def drinks_def by auto

lemma "drinks \<subseteq>\<^sup>r consumes"
  by (simp add: drinks_def subset_def)


(*****Miscellaneous*****)

(*Transitive closure*)
definition tran_closure::"ERel('i) \<Rightarrow> ERel('i)" ("_\<^sup>+")
  where \<open>r\<^sup>+ \<equiv> \<Inter>\<^sup>r(\<lambda>\<rho>. r \<subseteq>\<^sup>r \<rho> \<and> transitive \<rho>)\<close>

(*A typical example for transitive closure*)
definition \<open>ancestorOf \<equiv> parentOf\<^sup>+\<close>

term "Finite_Set"

(*Another example, involving dating*)
lemma assumes "symmetric(dates)"
          and "Klaus \<noteq> John \<and> Klaus \<noteq> Mary"
          and "Anne : \<^bold>\<forall>dates\<sqdot>{John,Mary}"
        shows "Klaus : \<^bold>\<exists>dates\<^sup>-\<sqdot>{Anne}"
  by (smt (verit, ccfv_SIG) Symmetric_def assms(1) assms(2) assms(3) compl_def rDualPreimage_def rPreimage_def)


(****************************************************************************)
(* Exercise: defining (qualified) number restrictions \<le>\<^sub>nr (\<le>\<^sub>nr.C)           *)
(****************************************************************************)

(* Useful(?) definitions*)
abbreviation diff_dia::"Set('i) \<Rightarrow> Set('i)" ("\<D>")
  where "\<D> \<equiv> rPreimage (\<noteq>)"

abbreviation morethan1::"Set('i) \<Rightarrow> bool" ("\<Sigma>\<^sub>>\<^sub>1_")
  where "\<Sigma>\<^sub>>\<^sub>1 S \<equiv> \<forall>P. S \<subseteq> P \<rightarrow> (S \<inter> (P \<inter> \<D> P) \<noteq> \<emptyset>)"
abbreviation morethan2::"Set('i) \<Rightarrow> bool" ("\<Sigma>\<^sub>>\<^sub>2_")
  where "\<Sigma>\<^sub>>\<^sub>2 S \<equiv> \<forall>P\<^sub>1 P\<^sub>2. (S \<subseteq> (P\<^sub>1 \<union> P\<^sub>2)) \<rightarrow> (S \<inter> ((P\<^sub>1 \<inter> \<D> P\<^sub>1) \<union> (P\<^sub>2 \<inter> \<D> P\<^sub>2)) \<noteq> \<emptyset>)"
(***Exercise: define for >3 and extrapolate for arbitrary n***)

lemma "\<Sigma>\<^sub>>\<^sub>1{a,b}" nitpick oops (*counterexample*)
lemma "a \<noteq> b \<longrightarrow> \<Sigma>\<^sub>>\<^sub>1 {a,b,c}" 
  by (smt (verit, del_insts) inter_def rPreimage_def subset_def)
lemma "\<Sigma>\<^sub>>\<^sub>2{a,b,c}" nitpick oops (*counterexample*)
lemma "a \<noteq> b \<and> a \<noteq> c \<and> c \<noteq> b \<longrightarrow> \<Sigma>\<^sub>>\<^sub>2{a,b,c}"
  unfolding inter_def rPreimage_def subset_def by (smt (verit, best) union_def) 


(* ... *)

end