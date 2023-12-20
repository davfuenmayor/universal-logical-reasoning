(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory FregeExampleLines2  (* Frege - Foundations of Arithmetic \<section>62-69  (part II) *)
imports "../../library/endorels"
begin

(*We could define what a "line" is (but we don't need to ;) ...*)
typedecl line

(*We could also define the relation of "being parallel" in terms of the definition of "line", but...
 It is easier to just axiomatize the notion: we say what are (some) 'essential properties' of parallelism *)
axiomatization parallel::"ERel(line)" (* line \<Rightarrow> (line \<Rightarrow> bool) *)
  where REFL: "reflexive parallel"
    and SYMM: "symmetric parallel"
    and TRAN: "transitive parallel"

(*or, in other words *)
lemma "equivalence parallel" unfolding equivalence_def using REFL SYMM TRAN by auto

(*We have introduced a new term (constant) into the language (via axiomatization)*)
term "parallel"
term "parallel::ERel(line)"
term "parallel::ERel*(line)"  (*error: wrong type*)
term "parallel \<langle>a,b\<rangle>" (*error: not a well-formed formula*)
term "parallel a b"

(*Some facts about parallelism follow from being an equivalence relation*)
lemma "parallel a b \<and> \<not>parallel c b \<rightarrow> \<not>parallel a c" by (metis SYMM Symmetric_def TRAN Transitive_def)

(*Now recall that relations are also set-valued functions, so the following statement is well-formed *)
term "parallel a" (*set of lines parallel to a*)

(*Frege defines the direction of a line as the set (equivalence class) of lines parallel to it *)
abbreviation(input) direction::"line \<Rightarrow> Set(line)"
  where "direction a \<equiv> \<lambda>x. (parallel a) x"

term "direction"
term "direction::line \<Rightarrow> Set(line)"
term "direction::ERel(line)"
term "direction a" (*the direction of line 'a' *)
term "parallel::line \<Rightarrow> Set(line)"
term "parallel a" (*the direction of line 'a' *)

(*but now note that (by eta-reduction)*)
lemma "direction = parallel" ..

(*The main statement: two lines are parallel iff their directions are identical*)
lemma main: "parallel a b = (direction a = direction b)" 
  by (metis REFL Reflexive_def SYMM Symmetric_def TRAN Transitive_def)

lemma main': "parallel a b = ((parallel a) = (parallel b))" using main by blast

(***** Beware: math jargon *****)
(*The set of the equivalence classes of a set S wrt. an equivalence relation R is called the "quotient set" 
or "quotient space" of S by R (denoted by "S/R". Read "S modulo R").

Thus, the set of directions is the "quotient" of the set of lines by the "parallel" relation.
            directions = lines/parallel ("lines modulo parallelism")
*)

(*We can encode the set of directions as the range of the direction/parallel function (that assigns a direction to a line)*)
abbreviation "Directions \<equiv> fRange parallel" 

(*In other words:*)
lemma "Directions = fImage parallel \<UU>" unfolding rel_defs func_defs by simp


(* The (equivalence) relation "parallel" is the kernel of the function "direction" *)
(*The "kernel" of a function 'f': the set of those pairs of objects which get the same value under 'f'.*)
definition kernel::"('a \<Rightarrow> 'b) \<Rightarrow> ERel('a)" ("ker")
  where "ker f \<equiv> \<lambda>x y. (f x) = (f y)"

lemma "(ker f) a b = (f a = f b)" by (simp add: kernel_def)


(*Parallelism/direction is its own kernel*)
lemma "(ker parallel) = parallel" 
  unfolding kernel_def apply((rule ext)+, rule sym, rule main) done


(**** Generalizing ****)

(*What we have seen holds indeed of any (equivalence) relation R when encoded as a set-valued function *)
term "(R x)::Set('a)" (*the image (equivalence class) of object x under R *)

(*We have in fact the following alternative definition of an equivalence relation:*)
lemma equivalence_char: "equivalence R = (\<forall>a b. R a b = (R a = R b))" 
  sorry (*this is a theorem (TODO: prove)*)

(*In other words: equivalence relations are the fixed-points of the kernel operation:*)
lemma "equivalence R \<longleftrightarrow> (R = (ker R))" unfolding kernel_def by (metis equivalence_char)

(*And we can even define the quotient of a set S by an equivalence relation R as: *)
(* definition quotient::"Set('a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> Set('b)" (infix "'/" 99) *)
definition quotient::"Set('a) \<Rightarrow> ERel('a) \<Rightarrow> Set(Set('a))" (infix "'/" 99)
  where "S / R = fImage R S" 

end