(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory FregeExampleLines1  (* Frege - Foundations of Arithmetic \<section>62-69  (part I) *)
imports "../../library/pairs"
begin

(*We could define what a "line" is (but we don't need to ;) ...*)
typedecl line

(*We could also define the relation of "being parallel" in terms of the definition of "line", but...
 It is easier to just axiomatize the notion: we say what are (some) 'essential properties' of parallelism *)
axiomatization parallel::"Pair(line) \<Rightarrow> bool"
  where REFL: "\<forall>x. parallel \<langle>x,x\<rangle>"
    and SYMM: "\<forall>x y. parallel \<langle>x,y\<rangle> \<rightarrow> parallel \<langle>y,x\<rangle>"
    and TRAN: "\<forall>x y z. parallel \<langle>x,y\<rangle> \<and> parallel \<langle>y,z\<rangle> \<rightarrow> parallel \<langle>x,z\<rangle>"

(*We have introduced a new term (constant) into the language (via axiomatization)*)
term "parallel"
term "parallel::ERel*(line)"
term "parallel \<langle>a,b\<rangle>"

(*Some facts about parallelism follow from being an equivalence relation*)
lemma "parallel \<langle>a,b\<rangle> \<and> \<not>parallel \<langle>c,b\<rangle> \<rightarrow> \<not>parallel \<langle>a,c\<rangle>" using SYMM TRAN by blast

(*Frege defines the direction of a line 'a' as the set (equivalence class) of lines parallel to a *)
definition direction::"line \<Rightarrow> Set(line)"
  where "direction a \<equiv> \<lambda>x. parallel \<langle>a,x\<rangle>"

(*We have introduced a new term into the language (via definition)*)
term "direction"
term "direction::ERel(line)"
term "(direction a)::Set(line)"
term "direction a b"


(*The main statement: two lines are parallel iff their directions are identical*)
lemma main: "parallel \<langle>a,b\<rangle> = (direction a = direction b)"
  unfolding direction_def by (meson REFL SYMM TRAN) 

(***** Beware: math jargon *****)
(*The set of the equivalence classes of a set S wrt. an equivalence relation R is called the "quotient set" 
or "quotient space" of S by R (denoted by "S/R". Read "S modulo R").

Thus, the set of directions is the "quotient" of the set of lines by the "parallel" relation.
            directions = lines/parallel ("lines modulo parallelism")
*)

(*The "kernel" of a function 'f': the set of those pairs of objects which get the same value under 'f'.*)
definition kernel::"('a \<Rightarrow> 'b) \<Rightarrow> ERel*('a)" ("ker")
  where "ker f \<equiv> \<lambda>p. f(\<pi>\<^sub>1 p) = f (\<pi>\<^sub>2 p)"

(*In other words: *)
lemma "(ker f)\<langle>a,b\<rangle> = (f a = f b)" by (simp add: kernel_def proj1_char proj2_char)

(*The (equivalence) relation "parallel" is the kernel of the function "direction".
Thus, the kernel operation gives us the way back from the notion of "direction" to the notion of "parallelism":*)
lemma "(ker direction) = parallel"
  unfolding direction_def kernel_def apply(rule ext) by (metis main mkPair_char)
end