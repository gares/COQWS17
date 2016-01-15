From mathcomp Require Import all_ssreflect.

(* some stuff *)

(** ** Recap:
   - => intro pattern (names, views, //, /=, {}, [])
   - rewrite lem -lem // /= /def
   - naming convention: addnC, eqP, orbN, orNb, ...
   - notations: .+1, if-is-then-else
   - reflect P b

*)

(** ** Spec lemmas
   - Inductive predicates to drive the proof
*)
CoInductive leq_xor_gtn m n : bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
by rewrite ltnNge; case le_mn: (m <= n); constructor; rewrite // ltnNge le_mn.
Qed.

(*
Lemma test_leqP m n1 n2 : (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Proof.
rewrite /minn ltnNge. case: (leqP n2 n1); case: (leqP m).
give_up.
wlog le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => ?; last rewrite minnC andbC; auto.
by rewrite /minn ltnNge le_n21 /= andbC; case: leqP => // /leq_trans->.
Qed.
*)

CoInductive compare_nat m n : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : compare_nat m n true false false
  | CompareNatGt of m > n : compare_nat m n false true false
  | CompareNatEq of m = n : compare_nat m n false false true.

Lemma ltngtP m n : compare_nat m n (m < n) (n < m) (m == n).
Proof.
rewrite ltn_neqAle eqn_leq; case: ltnP; first by constructor.
by rewrite leq_eqVlt orbC; case: leqP; constructor; first apply/eqnP.
Qed.



(** ** Sequences
  - an alias for lists (used to be differnt)
  - many notations
*)
Check [:: 3 ; 4].
Check [::] ++ [:: true ; false].
Eval compute in [seq x.+1 | x <- [:: 1; 2; 3]].
Eval compute in rcons [:: 4; 5] 3.
Eval compute in [seq x <- [::3; 4; 5] | odd x ].
Eval compute in 3 \in [:: 7; 4; 3].
Eval compute in all odd [:: 3; 5]. 

(* have, seq, elim/foo, case: leqP *)



