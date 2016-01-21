Require Import mathcomp.ssreflect.ssreflect.
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 
Classical logic is somewhat surprising!
Prove that given two arbitrary propositions
a and b, either a implies b or the converse *)

Lemma CL_is_wrong_and_boolrefl_is_nice (A B : (*D*)bool(*D*)) :
  (A -> B) \/ (B -> A).
(*A*)Proof. case: A; case: B; by [left | right]. Qed.

(** Enrico is a lazy student.  When asked to reverse and filter
a list he comes up with the following ugly code. *)

Fixpoint filtrev T (p : pred T) (acc : seq T) (l : seq T) : seq T :=
  if l is x :: xs then
    if p x then filtrev p (x :: acc) xs
           else filtrev p       acc  xs
  else acc.

(**  The teacher asks him to prove that his ugly code is equivalent
 to the nicer code [[seq x <- rev l | p x]] he could have written
by reusing the seq library.

Such proof is not trivial:
  - [filtrev] has an accumulator, [rev] (at least apparently)
    does not.
  - which is the invariant linking the accumulator [acc] and [p]
    in the code of [filtrev]?  Such invariant must be
    taken into account by the induction.

Relevant keywords for [Search] are: rev cons cat filter rcons
Hint: it is perfectly fine to state intermediate lemmas
*)

Lemma filterrev_ok T p (l : seq T) :
  filtrev p [::] l = [seq x <- rev l | p x ].
Proof.
(*X*)have: all p [::] by []; rewrite -[rev l]cats0.
(*X*)elim: l [::] => [? /all_filterP | x xs IH acc p_acc] //.
(*X*)case: (boolP (p x)) => [px | /negbTE n_px].
(*X*)  by rewrite /= px IH /= ?px // rev_cons cat_rcons.
(*X*)by rewrite rev_cons filter_cat filter_rcons /= n_px /= -filter_cat IH.
(*A*)Qed.

(** Prove that if (s1 :|: s2) is disjoint from (s1 :|: s3) then
    s1 is empty *)
Lemma disjoint_setU2l (T : finType) (s1 s2 s3 : {set T}) :
   [disjoint s1 :|: s2 & s1 :|: s3] -> s1 = set0.
Proof.
(*X*)move/pred0P=> H; apply/setP => x.
(*X*)by have := (H x); rewrite !inE; case: (_ \in _).
(*A*)Qed.

(** Prove the equivalence of these two sums.
    E.g. (n=8)
<<
    1 + 3 + 5 + 7 = 7-0 + 7-2 + 7-4 + 7-6
>>
*)
Lemma sum_odd n :
  ~~ odd n -> \sum_(i < n | odd i) i = \sum_(i < n | ~~ odd i) (n.-1 - i).
Proof.
(*X*)case: n => [|n Hn]; first by rewrite !big_ord0.
(*X*)rewrite (reindex_inj rev_ord_inj) /=.
(*X*)apply: eq_big => [i|i//].
(*X*)by rewrite odd_sub // (negPf Hn).
(*A*)Qed.

