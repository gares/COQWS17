Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.
(**
#<div class="slide vfill">#
** Recap:
   - => intro pattern (names, views, //, /=, {}, [[]])
   - rewrite lem -lem // /= /def
   - naming convention: addnC, eqP, orbN, orNb, ...
   - notations: .+1, if-is-then-else
   - reflect P b
   - Search _ (_ + _) in ssrnat.
   - Search _ addn "C" in ssrnat.
   - Use the HTML doc!

#</div>#
--------------------------------------------------------
#<div class="slide vfill">#
** Today:
   - The [seq] library
   - forward reasoning with [have]
   - spec lemmas
   - [rewrite] patterns

#</div>#
--------------------------------------------------------
--------------------------------------------------------
#<div class="slide">#
** Sequences:
  - an alias for lists (used to be differnt)
  - many notations

*)
Check [::].
Check [:: 3 ; 4].
Check [::] ++ [:: true ; false].
Eval compute in [seq x.+1 | x <- [:: 1; 2; 3]].
Eval compute in [seq x <- [::3; 4; 5] | odd x ].
Eval compute in rcons [:: 4; 5] 3.
Eval compute in all odd [:: 3; 5].

Module polylist.

(**
#</div>#
--------------------------------------------------------
#<div class="slide">#
** Polymorphic lists
   - This statement makes no assumptions on T
   - recap: // /= ->
*)
Lemma size_cat T (s1 s2 : seq T) : size (s1 ++ s2) = size s1 + size s2.
Proof.  by elim: s1 => //= x s1 ->. Qed.

End polylist.

Eval compute in 3 \in [:: 7; 4; 3].

Fail Check forall T : Type, forall x : T, x \in [:: x ].

(** 
#</div>#
--------------------------------------------------------
#<div class="slide">#
** Had-hoc polymorphism
  - T : Type |- l : list T 
  - T : eqType |- l : list T
  - eqType means: a type with a decidable equality (_ == _)
*)

Check forall T : eqType, forall x : T, x \in [:: x ].

(**
#</div>#
--------------------------------------------------------
#<div class="slide">#
** The \in notation
   - overloaded as [(_ == _)]
   - pushing \in with inE
   - computable.
   - rewrite !inE
*)
Lemma test_in l : 3 \in [:: 4; 5] ++ l -> l != [::].
Proof.
by rewrite !inE => /=; apply: contraL => /eqP->.
Qed.

(* Example of simplifying context *)
Eval simpl in (3 \in [:: 4; 3]). (* && *)

(**
#</div>#
--------------------------------------------------------
#<div class="slide">#
** Forward reasoning
   - have
   - have :=
   - have + views
   - do I need eqType here?
*)
(**
Definition of all
<<
Fixpoint all a s := if s is x :: s' then a x && all a s' else true.
>> *)
(** 
Definition of count
<<
Fixpoint count a s := if s is x :: s' then a x + count s' else 0.
>> *)
(** 
A lemma linking the two concepts *)
Lemma all_count (T : eqType) (a : pred T) s :
  all a s = (count a s == size s).
Proof.
elim: s => //= x s.
have EM_a : a x || ~~ a x.
  by exact: orbN.
move: EM_a => /orP EM_a. case: EM_a => [-> | /negbTE-> ] //= _.
(*# have /orP[ ax | n_ax ] : a x || ~~ a x by case: (a x). #*)
Search _ count size.
by rewrite add0n eqn_leq andbC ltnNge count_size.
Qed.

(**
#</div>#
--------------------------------------------------------
--------------------------------------------------------
#<div class="slide">#
** Spec lemmas
   - Inductive predicates to drive the proof
*)

Module myreflect1.

Inductive reflect (P : Prop) (b : bool) : Prop :=
  | ReflectT (p : P) (e : b = true)
  | ReflectF (np : ~ P) (e : b = false).

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

Axiom eqP : forall m n, reflect (m = n) (eqn m n).

Lemma test_reflect1 m n : ~~ (eqn m n) || (n <= m <= n).
Proof.
case: (eqn m n) => /=.
(*# case: (eqP m n) => [Enm -> | nE_mn ->] /=. #*)
Admitted.

End myreflect1.

(*#
Module myreflect2.

Inductive reflect (P : Prop) : bool-> Prop :=
  | ReflectT (p : P) : reflect P true
  | ReflectF (np : ~ P) : reflect P false.

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

Axiom eqP : forall m n, reflect (m = n) (eqn m n).

Lemma test_reflect1 m n : ~~ (eqn m n) || (n <= m <= n).
Proof.
case: (eqP m n) => [Enm | nE_mn ] /=.
by case: eqP => [->|] //=; rewrite leqnn.
Check (eqP _ _).
Qed.

End myreflect2.
#*)

Inductive leq_xor_gtn m n : bool -> bool -> Prop :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Axiom leqP : forall m n : nat, leq_xor_gtn m n (m <= n) (n < m).

(**
#</div>#
--------------------------------------------------------
#<div class="slide">#
** Let's try out leqP on an ugly goal
   - matching of indexes
   - generalization of unresolved implicits
   - instantiation by matching
*)
Lemma test_leqP m n1 n2 :
  (m <= (if n1 < n2 then n1 else n2)) =
  (m <= n1) && (m <= n2) && ((n1 < n2) || (n2 <= n1)).
Proof.
case: leqP => [leqn21 | /ltnW ltn12 ]; rewrite /= andbT.
  by rewrite andb_idl // => /leq_trans /(_ leqn21).
by rewrite andb_idr // => /leq_trans->.
Qed.

(**
#</div>#
--------------------------------------------------------
#<div class="slide">#
** Another commodity: [ifP]
   - a spec lemma for if-then-else
   - handy with case, since matching spares you to write
     the expressions involved
*)
Lemma test_ifP n m : if n <= m then 0 <= m - n else m - n == 0.
Proof.
case: ifP; first by rewrite -subn_eq0.
by move=> /negbT; rewrite subn_eq0 leqNgt negbK=> /ltnW.
Qed.

(**
#</div>#
--------------------------------------------------------
#<div class="slide">#
** Last, (_ =P _)
  - Just eqP but with the right implicit arguments
*)
Lemma test_eqP (n m : nat) : n == m.
Proof. case: (n =P m). Abort.

(**
#</div>#
--------------------------------------------------------
#<div class="slide">#
** Rewrite on steroids
   - keyed matching
   - instantiation
   - localization
*)
Lemma ugly_goal n m :
  n + (m * 2).+1 = n + (m + m.+1).
Proof.
rewrite addnC.
rewrite (addnC m).
rewrite [_ + m]addnC.
rewrite [in n + _]addnC.
rewrite [X in _ = X + n]addnC.
rewrite [in RHS]addnC.
Abort.

Lemma ugly_goal n m :
  n + m = n + m.
Proof.
rewrite addnC.
rewrite [in RHS]addnC.
Abort.

Lemma no_pattern n : n + 0 = n.
Proof.
rewrite -[n in RHS]addn0.
Abort.

(**
#</div>#
--------------------------------------------------------
#<div class="slide vfill">#
** References for this lesson:
  - SSReflect #<a href="https://hal.inria.fr/inria-00258384">manual</a>#
  - documentation of the
       #<a href="http://math-comp.github.io/math-comp/htmldoc/libgraph.html">library</a>#
    - in particular #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.seq.html">seq</a>#

#</div>#
--------------------------------------------------------
#<div class="slide">#
** Demo:
   - you should be now able to read this proof

*)

Lemma dvdn_fact m n : 0 < m <= n -> m %| n`!.
Proof.
case: m => //= m; elim: n => //= n IHn; rewrite ltnS leq_eqVlt.
by move=> /orP[ /eqP-> | /IHn]; [apply: dvdn_mulr | apply: dvdn_mull].
Qed.

Lemma prime_above m : {p | m < p & prime p}.
Proof.
Check pdivP.
have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1 by rewrite addn1 ltnS fact_gt0.
exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
Check dvdn_addr.
by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
    
(** #</div># *)


