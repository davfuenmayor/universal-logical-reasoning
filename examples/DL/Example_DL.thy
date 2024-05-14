(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory Example_DL
  imports "DescriptionLogic"
begin



subsection \<open>Example 1 - Knowledge Base\<close>

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


(*TBox ('terminological box' or 'ontology')*)
axiomatization where
  T1: "Writer \<^bold>\<equiv> (Person \<^bold>\<sqinter> \<^bold>\<exists>author\<sqdot>Book)" and
  T2: "Novel \<^bold>\<sqsubseteq> Book"
(* .... *)

(*ABox ('assertional box')*)
axiomatization where
  A1: "GeorgeOrwell : Person" and
  A2: "AnimalFarm : Novel" and
  A3: "(GeorgeOrwell, AnimalFarm) : author" and
  A4: "(GeorgeOrwell, Bihar) : bornIn" and
  A5: "(Bihar, India) : cityOf"
(* .... *)

(* Given the background knowledge, we can infer that GeorgeOrwell is a writer*)
lemma "GeorgeOrwell : Writer"
  by (metis (full_types) A1 A2 A3 T1 T2 inter_def relPreimage_def subset_def)

(* Can we infer that GeorgeOrwell is European?*)
lemma "GeorgeOrwell : European" nitpick oops (*countermodel found: background knowledge is missing *)

(*adds further background knowledge to TBox and ABox*)
axiomatization where
(* .... *)
  T3: "British \<^bold>\<sqsubseteq> European" and
(* .... *)
  A6: "GeorgeOrwell : British" (*is he?*)
(* .... *)

(*Now we can in fact infer that GeorgeOrwell is European (given the background information)*)
lemma "GeorgeOrwell : European" (*is he?*)
  by (meson A6 T3 subset_def)


(*Exercise*)

(*John is a blogger (and wannabe writer) who likes to show off that he is the grandson of Mr Orwell 
 (from whom he supposedly inherited his writing skills). 

Encode the following statements (preferably as theorems): 

- John is the grandson of GeorgeOrwell
- GeorgeOrwell is talented
- talent is inherited (you might need to paraphrase this a bit, maybe in terms of 'ancestor', etc.)
- John is talented
*)

(*The solution show look like:*)
consts X::r (*some role*)
consts Y::c (*some concept*)

axiomatization where
   J1: "True"   and (*replace placeholder with something like: John is child of someone who is child of Mr Orwell*)
   J2: "True" and (*Mr Orwell is talented (as a writer)*)
   J3: "True"    (*talent is inherited (be creative!)*)
   (*... (maybe something else) *)

theorem "True" oops (*John is a talented writer (or just "John is talented" depending on the granularity of the modelling)*)



end
