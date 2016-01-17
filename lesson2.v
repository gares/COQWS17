From mathcomp Require Import all_ssreflect.

(** ** Recap:
   - => intro pattern (names, views, //, /=, {}, [])
   - rewrite lem -lem // /= /def
   - naming convention: addnC, eqP, orbN, orNb, ...
   - notations: .+1, if-is-then-else
   - reflect P b

----
** Today:
   - The seq library
   - forward reasoning with [have]
   - spec lemmas
   - rewrite patterns

----
** Sequences
  - an alias for lists (used to be differnt)
  - many notations
*)
Check [:: 3 ; 4].
Check [::] ++ [:: true ; false].
Eval compute in [seq x.+1 | x <- [:: 1; 2; 3]].
Eval compute in rcons [:: 4; 5] 3.
Eval compute in [seq x <- [::3; 4; 5] | odd x ].
Eval compute in all odd [:: 3; 5].

Module poly.

Lemma size_cat T (s1 s2 : seq T) : size (s1 ++ s2) = size s1 + size s2.
Proof. by elim: s1 => //= x s1 ->. Qed.

End poly.

Eval compute in 3 \in [:: 7; 4; 3].

Fail Check forall T : Type, forall x : T, x \in [:: x ].

(** 
----
** Had-hoc polymorphism
  - T : Type |- l : list A  !=  T : eqType |- l : list T
  - eqType means: a type with a decidable equality (_ == _)
*)

Check forall T : eqType, forall x : T, x \in [:: x ].

(**
----
** The \in notation
   - overloaded as [(_ == _)]
   - pushing \in with inE
   - computable.
   - rewrite !inE
*)
Lemma test_in l : 3 \in [:: 4; 5] ++ l -> l != [::].
Proof.
by rewrite !inE => /=; apply: contraL => /eqP->; rewrite in_nil.
Qed.

(** Forward reasoning
   - have
   - have + views
*)
(**
Definition of all
<<
Fixpoint all s := if s is x :: s' then a x && all s' else true.
>>
Definition of count
<<
Fixpoint count s := if s is x :: s' then a x + count s' else 0.
>>
A lemma linking the two concepts *)
Lemma all_count (T : eqType) (a : pred T) s : all a s = (count a s == size s).
Proof.
elim: s => //= x s.
(* case: (a x) => _ //=.*)
(*# have /orP[ ax | n_ax ] : a x || ~~ a x by case: (a x). #*)
have [// | a'x _ /=] := boolP (a x).
Search _ count size.
rewrite add0n eqn_leq. rewrite andbC.
rewrite ltnNge. by rewrite count_size.
Qed.

(**
----
** Spec lemmas
   - Inductive predicates to drive the proof
*)

Inductive leq_xor_gtn m n : bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
by rewrite ltnNge; case le_mn: (m <= n); constructor; rewrite // ltnNge le_mn.
Qed.

Lemma test_leqP m n1 n2 : (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Proof.
rewrite /minn; case: (leqP n2 n1); case: (leqP m); rewrite ?andbF //=.
  by move=> /leq_trans-H /H->.
by move=> /leq_trans-H /ltnW /H->.
Qed.

(** Another spec
<<
Inductive compare_nat m n : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : compare_nat m n true false false
  | CompareNatGt of m > n : compare_nat m n false true false
  | CompareNatEq of m = n : compare_nat m n false false true.
>>
And the relevant lemma using it
*)
Lemma ltngtP m n : compare_nat m n (m < n) (n < m) (m == n).
Proof.
rewrite ltn_neqAle eqn_leq; case: ltnP; first by constructor.
by rewrite leq_eqVlt orbC; case: leqP; constructor; first apply/eqnP.
Qed.

(**
----
** Another commodity: [ifP]
   - a spec lemma for if-then-else
   - handy with case, since matching spares you to write
     the expressions involved
*)
Lemma test_ifP n m : if n <= m then 0 <= m - n else m - n == 0.
Proof.
case: ifP; first by rewrite -subn_eq0.
by move/negbT; rewrite subn_eq0 leqNgt negbK=> /ltnW.
Qed.

(** TODO
- eqP is also (x =P y).
- boolP
- rewrite [in RHS]
*)

(**
----
** References for this lesson:
  - SSReflect #<a href="https://hal.inria.fr/inria-00258384">manual</a>#
  - documentation of the
       #<a href="http://math-comp.github.io/math-comp/htmldoc/libgraph.html">library</a>#
    - in particular #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.seq.html">seq</a>#

*)
