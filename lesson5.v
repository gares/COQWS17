From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
(**

* The algebra library

 - This is a central part of the mathematical components library.
 - This library register a various range of (mathematical) structures.
  - types with decidable equality: eqType
  - types with a finite number of elements: finType
  - finite groups: finGroupType
  - abelian (not possibly finite) groups: zmodType
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

- Some of these structures share operators: e.g. the operator (_ + _),
  introduced for abelian groups (zmodType), is also available for all
  the structures that require it (rings, domains, fields, etc...)

- All of these structures are discrete: they all have decidable
  equality: the operator (_ == _) is available on all of them.

- #<a href="http://www-sop.inria.fr/teams/marelle/advanced-coq-16/mc_hieralg.pdf">  Here is a picture of the begining of the hierarchy</a>#
  Extensive documentation in the header of:
 - #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssralg.html">ssralg</a>#
 - #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.algebra.ssrnum.html">ssrnum</a>#

- In addition there are structures for maps (additive morphisms, ring
  morphisms, etc...), and substructures (subgroup, subsemiring, subring,
  subfield, etc...)


----

* Roadmap for the lesson:
 - introduction of the general definition pattern for algebraic structures
 - instantiation of a structure in the library
 - exploration of the theory provided by this structure and naming
   conventions
 - creation of a subalgebraic structure predicate and use


----
*)
Module AlgebraicStructures.
(**

----
* Defining a mathematical structure in Coq.

This is how mathematical structures are defined in the library.
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

End AlgebraicStructures.
(**

This packaging is very elementary, and the mathematical components
library uses a refinement of this.


----
* Packaging mathematical structures

We briefly explain how to do inheritance with two structures. This is
another simplified version of what happens in the library.  The
complete process is described in #<a
href="https://hal.inria.fr/inria-00368403v1/document">Packaging
Mathematical Structures (Garillot, Gonthier, Mahboubi, Rideau)</a>

*)
Section AlgebraicStructuresInheritance.

Record my_mixin1 dom := My_mixin1 {
(* symbols: constants and operators *)
  my_c    : dom;
  my_op   : dom -> dom -> dom;
(* axioms: properties on the symbols *)
  my_opxc : forall x, my_op x my_c = my_c;
  my_opC : forall x y, my_op x y = my_op y x
}.

Definition my_class1 := my_mixin1.

Structure my_struct1 := My_struct1 {
(* domain/carrier/sort of the structure *)
  dom1 :> Type;
  class1 : my_mixin1 dom1;
}.

Definition op {s : my_struct1} := my_op (class1 s).
Definition c {s : my_struct1} := my_c (class1 s).
Notation "x * y" := (op x y).

Record my_mixin2 (dom : my_struct1) := My_mixin2 {
(* symbols: constants and operators *)
  my_pred   : pred dom;
(* axioms: properties on the symbols *)
  my_predc : forall x, my_pred (op c x)
}.

Record my_class2 dom := My_class2 {
  base2 :> my_class1 dom;
  mixin2 :> my_mixin2 (@My_struct1 dom base2);
}.

Structure my_struct2 := My_struct2 {
  dom2  :> Type;
  class2 : my_class2 dom2;
}.

Definition pr {s : my_struct2} := my_pred (class2 s).

Canonical my_struct1_2 (s : my_struct2) : my_struct1 :=
  @My_struct1 (dom2 s) (class2 s : my_class1 _).

Section my_struct1_theory.

Variable s : my_struct1.

Lemma opC (x y : s) : x * y = y * x.
Proof. by case: s x y => ? []. Qed.

Lemma opxc (x : s) : x * c = c.
Proof. by case: s x => ? []. Qed.

(* Theory of the structure *)
Lemma opcx (x : s) : c * x = c.
Proof. by rewrite opC opxc. Qed.

End my_struct1_theory.

Section my_struct2_theory.

Variable s : my_struct2.

Lemma pr_xc (x : s) : pr (c * x).
Proof. by case: s x => ? [? []]. Qed.

Lemma pr_c : pr (c : s).
Proof. by rewrite -(opcx c) pr_xc. Qed.

End my_struct2_theory.

End AlgebraicStructuresInheritance.
(**

----
* Inhabiting the mathematical structures hierarchy.

 - We now show on the example of integers how to instantiate the
   mathematical structures that integers satisfy.

 - As a step to minimize the work of the user, the library provides a
   way to provide only the mixin. The general pattern is to build the
   mixin of a structure, declare the canonical structure associated
   with it and go one with creating the next mixin and creating the new
   structure. Each time we build a new structure, we provide only the
   mixin, as the class can be inferred from the previous canonical
   structures

 - We now show three different ways to build mixins here and an
   additional fourth will be shown in the exercices

  - using a reference structure,
  - building the required mixin from scratch,
  - building a more informative mixin and using it for a weaker structure,
  - (in the example) by subtyping.

*)
Module InstantiationInteger.

From mathcomp Require Import ssralg.
Import GRing.Theory.
Local Open Scope ring_scope.

(**

** First we define int

*)
CoInductive int : Set := Posz of nat | Negz of nat.
Local Coercion Posz : nat >-> int.

Notation "n %:Z" := (Posz n)
  (at level 2, left associativity, format "n %:Z", only parsing).
(**

** Equality, countable and choice types, by injection

We provide an injection with explicit partial inverse, grom int to nat
+ nat, this will be enough to provide the mixins for equality,
countable and choice types.

*)
Definition natsum_of_int (m : int) : nat + nat :=
  match m with Posz p => inl _ p | Negz n => inr _ n end.

Definition int_of_natsum (m : nat + nat) :=
  match m with inl p => Posz p | inr n => Negz n end.

Lemma natsum_of_intK : cancel natsum_of_int int_of_natsum.
Proof. by case. Qed.
(**

We create the mixins for equality, countable and choice types from
this injection, and gradually inhabit the hierarchy. Try to swap any
of the three blocks to see what happen.

*)
Definition int_eqMixin := CanEqMixin natsum_of_intK.
Canonical int_eqType := EqType int int_eqMixin.

Definition int_choiceMixin := CanChoiceMixin natsum_of_intK.
Canonical int_choiceType := ChoiceType int int_choiceMixin.

Definition int_countMixin := CanCountMixin natsum_of_intK.
Canonical int_countType := CountType int int_countMixin.
(**

** Abelian group structure, from scratch

We now create the abelian group structure of integers (here called
Z-module), from scratch, introducing the operators and proving exactly
the required properties.

*)
Module intZmod.
Section intZmod.

Definition addz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => Posz (m' + n')
    | Negz m', Negz n' => Negz (m' + n').+1
    | Posz m', Negz n' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
    | Negz n', Posz m' => if n' < m' then Posz (m' - n'.+1) else Negz (n' - m')
  end.

Definition oppz m := nosimpl
  match m with
    | Posz n => if n is (n'.+1)%N then Negz n' else Posz 0
    | Negz n => Posz (n.+1)%N
  end.

Lemma addzC : commutative addz. Admitted.
Lemma add0z : left_id (Posz 0) addz. Admitted.
Lemma oppzK : involutive oppz. Admitted.
Lemma addzA : associative addz. Admitted.
Lemma addNz : left_inverse (Posz 0) oppz addz. Admitted.

Definition Mixin := ZmodMixin addzA addzC add0z addNz.

End intZmod.
End intZmod.

Canonical int_ZmodType := ZmodType int intZmod.Mixin.
(**

Remark: we may develop here a piece of abelian group theory which is
specific to the theory of integers.

*)
Section intZmoduleTheory.

Lemma PoszD : {morph Posz : n m / (n + m)%N >-> n + m}.
Proof. by []. Qed.

End intZmoduleTheory.
(**

*** Ring and Commutative ring structure, the stronger the better

This time, we will build directly a rich commutative ring mixin first
and use it to instanciate both the ring structure and the commutative
ring struture at the same time. This is not only a structural economy
of space, but a mathematical economy of proofs, since the
commutativity property reduces the number of ring axioms to prove.

*)

Module intRing.
Section intRing.

Definition mulz (m n : int) :=
  match m, n with
    | Posz m', Posz n' => (m' * n')%N%:Z
    | Negz m', Negz n' => (m'.+1%N * n'.+1%N)%N%:Z
    | Posz m', Negz n' => - (m' * (n'.+1%N))%N%:Z
    | Negz n', Posz m' => - (m' * (n'.+1%N))%N%:Z
  end.

Lemma mulzA : associative mulz. Admitted.
Lemma mulzC : commutative mulz. Admitted.
Lemma mul1z : left_id (Posz 1) mulz. Admitted.
Lemma mulz_addl : left_distributive mulz (+%R). Admitted.
Lemma onez_neq0 : (Posz 1) != 0. Proof. by []. Qed.

Definition comMixin := ComRingMixin mulzA mulzC mul1z mulz_addl onez_neq0.

End intRing.
End intRing.

Canonical int_Ring := RingType int intRing.comMixin.
Canonical int_comRing := ComRingType int intRing.mulzC.

End InstantiationInteger.
(**
----
* Other structures
*)
Module OtherStructures.
From mathcomp Require Import ssralg ssrnum.
Import GRing.Theory.
Local Open Scope ring_scope.
(**
** Extensions of rings

- read the documentation of ssralg and ssrnum (algebraic structures
  with order)

** Structures for morphisms
*)

Search "linear" in ssralg.

Search "raddf" in ssralg.

Search "rmorph" in ssralg.
(**
** Substructures
*)

Print ssralg.GRing.subring_closed.
Print ssralg.GRing.subr_2closed.
Print ssralg.GRing.mulr_2closed.

Search "rpred" in ssralg.

End OtherStructures.
(**
----
* Naming conventions.
*)
Module Conventions.
From mathcomp Require Import ssralg ssrnum.
Import GRing.Theory.
Local Open Scope ring_scope.

(**
** Names in the library are usually obeying one of following the convention:

 - #<pre>(condition_)?mainSymbol_suffixes</pre>#
 - #<pre>mainSymbol_suffixes(_condition)?</pre>#

Or in the presence of a property denoted by a nary or unary predicate:
 - #<pre>naryPredicate_mainSymbol+</pre>#
 - #<pre>mainSymbol_unaryPredicate</pre>#

Where :

 - "mainSymbol" is the most meaningful part of the lemma. It generally
   is the head symbol of the right-hand side of an equation or the
   head symbol of a theorem. It can also simply be the main object of
   study, head symbol or not. It is usually either

  - one of the main symbols of the theory at hand. For example, for
    ssralg, it will be "opp", "add", "mul", etc...

  - or a special "canonical" operation, such as a ring morphism or a
    subtype predicate. e.g. "linear", "raddf", "rmorph", "rpred", etc ...

 - "condition" is used when the lemma applies under some hypothesis. As in

 - "suffixes" are there to refine what shape and/or what other symbols
   the lemma has. It can either be the name of a symbol ("add", "mul",
   etc...), or the (short) name of a predicate ("inj" for
   "injectivity", "id" for "identity", ...) or an abbreviation. We
   list here the main abbreviations.

  - A -- associativity, as in andbA : associative andb.
  - AC -- right commutativity.
  - ACA -- self-interchange (inner commutativity), e.g.,
        orbACA : (a || b) || (c || d) = (a || c) || (b || d).
  - b -- a boolean argument, as in andbb : idempotent andb.
  - C -- commutativity, as in andbC : commutative andb,
    or predicate complement, as in predC.
  - CA -- left commutativity.
  - D -- predicate difference, as in predD.
  - E -- elimination, as in negbFE : ~~ b = false -> b.
  - F or f -- boolean false, as in andbF : b && false = false.
  - I -- left/right injectivity, as in addbI : right_injective addb or predicate  intersection, as in predI.
  - l -- a left-hand operation, as andb_orl : left_distributive andb orb.
  - N or n -- boolean negation, as in andbN : a && (~~ a) = false.
  - P -- a characteristic property, often a reflection lemma, as in andP : reflec t (a /\ b) (a && b).
  - r -- a right-hand operation, as orb_andr : rightt_distributive orb andb.
  - T or t -- boolean truth, as in andbT: right_id true andb.
  - U -- predicate union, as in predU.
  - W -- weakening, as in in1W : {in D, forall x, P} -> forall x, P.

  - 0 -- ring 0, as in addr0 : x + 0 = x.
  - 1 -- ring 1, as in mulr1 : x * 1 = x.
  - D -- ring addition, as in linearD : f (u + v) = f u + f v.
  - B -- ring subtraction, as in opprB : - (x - y) = y - x.
  - M -- ring multiplication, as in invfM : (x * y)^-1 = x^-1 * y^-1.
  - Mn -- ring by nat multiplication, as in raddfMn : f (x *+ n) = f x *+ n.
  - N -- ring opposite, as in mulNr : (- x) * y = - (x * y).
  - V -- ring inverse, as in mulVr : x^-1 * x = 1.
  - X -- ring exponentiation, as in rmorphX : f (x ^+ n) = f x ^+ n.
  - Z -- (left) module scaling, as in linearZ : f (a *: v)  = s *: f v.


** This is design to help search. My own search strategy is usually.

- #<pre>Search _ "suffix1" "suffix2" (symbol|pattern)* in library.</pre>#


** Examples:
*)

Search _ *%R "A".

Search _ "unit" in ssralg.

Search _ "inj" in ssralg.

Search _ "rmorph" "M".

Search _ "rpred" "D".


End Conventions.

