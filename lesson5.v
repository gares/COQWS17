(** The algebra library

This is a central part of the mathematical components library.
This library register a various range of (mathematical) structures.
 - types with decidable equality: eqType
 - types with a finite number of elements: finType
 - finite groups: finGroupType
 - abelian (infinite) groups: zmodType
 - rings: ringType
 - rings with invertible elements: unitRingType
 - commutative rings: comRingType
 - integral domains: idomainType
 - fields: fieldType
 - left modules: lmodType
 - left algebra: lalgType
 - algebra: algType
 - finite dimensional vector spaces: vectType
 - ...

Some of these structures share operators: e.g. the operator (_ + _),
introduced for abelian groups (zmodType), is also available for all
the structures that require it (rings, domains, fields, etc...)

All of these structures are discrete: they all have decidable
equality: the operator (_ == _) is available on all of them.

In addition there are structures for maps (additive morphism, ring  and substructures.

----

Roadmap for the lesson:
 - introduction of the general definition pattern for algebraic structures
 - instantiation of a structure in the library
 - exploration of the theory provided by this structure and naming
   conventions
 - creation of a subalgebraic structure predicate and use
*)

From mathcomp Require Import all_ssreflect all_algebra.


Module AlgebraicStructuresTypicalScheme1.
(** This is how mathematical structures are defined in the library.
Unless you need to add a new mathematical structure to the library,
you will only need to read this.
*)

Structure my_struct := My_struct {
(* domain/carrier/sort of the structure *)
  dom  : Type;

(* symbols: constants and operators *)
  c    : dom;
  op   : dom -> dom -> dom;

(* axioms: properties on the symbols *)
  opxc : forall x, op x c = c;
  opC : forall x y, op x y = op y x
}.

(* Notations and modifiers for the symbols *)
Arguments op {m} x y.
Arguments c {m}.
Notation "x * y" := (op x y).

Section my_struct_theory.

Variable s : my_struct.

(* Theory of the structure *)
Lemma opcx (x : dom s) : c * x = c.
Proof. by rewrite opC opxc. Qed.

End my_struct_theory.

End AlgebraicStructuresTypicalScheme1.

Section AlgebraicStructuresTypicalScheme2.
End AlgebraicStructuresTypicalScheme2.

(* End of the lessson *)



