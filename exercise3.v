From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(**
  ----
  ** Exercise 1 *)

(**
Try to define a next function over 'I_n that correspond to the
successor function over the natural plus the special case that
"n -1" is mapped to zero *)

Definition onext n (x : 'I_n) : 'I_n.
Defined.

(**
  ----
  ** Exercise 2 
*)

(**
   Show that injectivity is decidable for a function f : aT -> rT
   with  aT a finite 
*) 

Check injective.

Definition injectiveb (aT : finType) (rT : eqType) (f : aT -> rT) : bool.
Defined.


Lemma injectiveP (aT : finType) (rT : eqType) (f : aT -> rT) : 
  reflect (injective f) (injectiveb f).
Proof.
Qed.

(** 
  ----
  ** Exercise 3 
*)

(** 
   Try to formalize the following problem 
*)

(** 
  Given a parking  where the boolean indicates if the slot is occupied or not 
*)

Definition parking n := 'I_n -> 'I_n -> bool.

(**
   Number of cars at line i 
*)               

Definition sumL n (p : parking n) i := \sum_(j < n) p i j.

(**
   Number of cars at column j 
*)

Definition sumC n (p : parking n) j := \sum_(i < n) p i j.

(**
   Show that if 0 < n there is always two lines, or two columns, or a column and a line
   that have the same numbers of cars 
*)

(** 
  ----
  ** Exercise 4 
*)

(** 
   Prove the following state by induction and by following Gauss proof.
 *)

Check sum_nat_const.

Lemma gauss_ex : forall n, (\sum_(i < n) i).*2 = n * n.-1.
Proof.
Qed.

(** 
  ----
   ** Exercise 5 
*)

Lemma sum_odd1 : forall n, \sum_(i < n) (2 * i + 1) = n ^ 2.
Proof.
Qed.

(** 
  ----
  ** Exercise 6 
*)

Lemma sum_exp : forall x n, 0 < x -> x ^ n.+1 - 1 = (x - 1) * \sum_(i < n.+1) x ^ i.
Proof.
Qed.

(**
  ----
 ** Exercise 7 
*)

(** Prove the following state by induction and by using a similar trick
   as for Gauss noticing that n ^ 3 = n * (n ^ 2) *)

Lemma bound_square : forall n, \sum_(i < n) i ^ 2 <= n ^ 3.
Proof.
Qed.

(**
  ----
  ** Exercise 8 
*)

(**
  building a monoid law 
*)

Section cex.

Variable op2 : nat -> nat -> nat.

Hypothesis op2n0 : right_id 0 op2.

Hypothesis op20n : left_id 0 op2.

Hypothesis op2A : associative op2.

Hypothesis op2add : forall x y, op2 x y = x + y.

Canonical Structure op2Mon : Monoid.law 0 :=
  Monoid.Law op2A op20n op2n0.

Lemma ex_op2 : \big[op2/0]_(i < 3) i = 3.
Proof.
Qed.

End cex.




