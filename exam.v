Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Lemma CL_is_wrong_and_boolrefl_is_nice (a b : bool) :
  (a -> b) \/ (b -> a).
Proof.  case: a; case: b; by [left | right]. Qed.

Definition myrev T (l : seq T) : seq T :=
  foldl (fun acc x => cons x acc) [::] l.
(*
They need a hint that myrev has an accumulator,
while rev does not.  The real lemma is
  rev s ++ acc = foldl cons^~ acc s
*)
Lemma myrev_is_rev T (l : seq T) :
  rev l = myrev l.
Proof.
rewrite -[rev l]cats0 /myrev.
elim: l [::] => //= x xs IHxs tl.
by rewrite rev_cons cat_rcons IHxs. 
Qed.


Lemma disjoint_setU2l (T : finType) (s1 s2 s3 : {set T}) :
   [disjoint s1 :|: s2 & s1 :|: s3] -> s1 = set0.
Proof.
move/pred0P=> H; apply/setP => x.
by have := (H x); rewrite !inE; case: (_ \in _).
Qed.

Lemma sum_odd n :
  ~~ odd n -> \sum_(i < n | odd i) i = \sum_(i < n | ~~ odd i) (n.-1 - i).
Proof.
case: n => [|n Hn]; first by rewrite !big_ord0.
rewrite (reindex_inj rev_ord_inj) /=.
apply: eq_big => [i|i//].
by rewrite odd_sub // (negPf Hn).
Qed.

