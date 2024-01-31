(**************************************************************)
(*           Copyright (c) 2023 David Fuenmayor               *)
(*       MIT License (see LICENSE file for details)           *)
(**************************************************************)
theory types (* Notation for type constructors *)
imports base
begin

section \<open>Type Constructors\<close>

(*Classifiers and indexers*)
type_synonym ('v,'a)Class = "'a \<Rightarrow> 'v" ("_-Class'(_')" [99])
type_synonym ('w,'a)Index = "'w \<Rightarrow> 'a" ("_-Index'(_')" [99])

(*Sets and pairs as unary type constructors*)
type_synonym ('a)Set = "o-Class('a)" ("Set(_)" [99])    (*same as: 'a \<Rightarrow> o *)
type_synonym ('a)Pair = "o-Index('a)" ("Pair(_)" [99])  (*same as: o \<Rightarrow> 'a *)

(*(Heterogeneous) relations between two types of objects as binary type constructors *)
type_synonym ('a,'b)Rel = "'a-Index(Set('b))" ("Rel'(_,_')" [99]) (*same as: 'a \<Rightarrow> ('b \<Rightarrow> o) *)
(* (Endo)relations on the same type of object as a special kind of relations *)
type_synonym ('a)ERel = "Rel('a,'a)" ("ERel(_)" [99])  (*same as: 'a \<Rightarrow> ('a \<Rightarrow> o) *)


(*As a convenient mathematical abstraction, we introduce the notion of "operation".
In mathematical phraseology, operations are said to 'operate' on (one or more) operands.
Thus, operations can be seen as (curried) functions whose arguments have all the same type.*)

(*Unary case: (endo)operations just correspond to (endo)functions*)
type_synonym ('a,'b)Op1 = "'a \<Rightarrow> 'b" ("Op'(_,_')" [99])
type_synonym ('a)EOp1 = "Op('a,'a)" ("EOp(_)" [99]) (* same as: 'a \<Rightarrow> 'a *)

(*Binary case: (endo)bi-operations correspond to curried (endo)bi-functions*)
type_synonym ('a,'b)Op2 = "'a \<Rightarrow> 'a \<Rightarrow> 'b" ("Op\<^sub>2'(_,_')" [99])
type_synonym ('a)EOp2 = "Op\<^sub>2('a,'a)" ("EOp\<^sub>2(_)" [99]) (* same as: 'a \<Rightarrow> ('a \<Rightarrow> 'a) *)

(*Arbitrary case: (endo)N-operations correspond to (endo)functions on sets*)
type_synonym ('a,'b)OpN = "Op(Set('a),'b)" ("Op\<^sub>N'(_,_')" [99])
type_synonym ('a)EOpN = "Op\<^sub>N('a,'a)" ("EOp\<^sub>N(_)" [99]) (* same as: Set('a) \<Rightarrow> 'a *)

(*In fact, binary operations can also be seen as unary operations on pairs, via currying*)
type_synonym ('a,'b)Op2star = "Op(Pair('a),'b)" ("Op\<^sub>2*'(_,_')" [99]) (* same as: (o \<Rightarrow> 'a) \<Rightarrow> 'b *)
type_synonym ('a)EOp2star = "Op\<^sub>2*('a,'a)" ("EOp\<^sub>2*(_)" [99]) (* same as: (o \<Rightarrow> 'a) \<Rightarrow> 'a *)

(*An alternative (isomorphic) characterization of endo-relations as binary operations with boolean codomain*)
type_synonym ('a)ERelstar = "Op\<^sub>2*('a,o)" ("ERel*(_)" [99]) (* same as: (o \<Rightarrow> 'a) \<Rightarrow> o *)

end