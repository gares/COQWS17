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


From mathcomp Require Import  all_algebra.

Section Polynomes.

Open Scope ring_scope.
Import GRing.Theory Num.Theory.

Variable n : nat.
Variables na nb: nat.
Hypothesis nbne0: nb != 0%N.

Definition a:rat := (Posz na)%:~R.
Definition b:rat :=(Posz nb)%:~R.

Definition pi := a / b. 

Definition f :{poly rat} := (n`!)%:R^-1 *: ('X^n * (a%:P -  b*:'X)^+n).

Definition F :{poly rat} := \sum_(i:'I_n.+1) (-1)^i *: f^`(2*i).


Axiom derive_f_0_int: forall i, f^`(i).[0] \is a Qint.


(** Prove that F at 0 is a Qint.  Hint: relevant lemmas
are exprnP hornerE horner_sum and the rpred* family *)
Lemma F0_int : F.[0] \is a Qint.
Proof.
(*X*)rewrite /F horner_sum rpred_sum // =>  i _ ; rewrite !hornerE rpredM //.
(*X*)  by rewrite -exprnP rpredX.
(*X*)by rewrite derive_f_0_int.
(*A*)Qed.

Axiom pf_sym:  f \Po (pi%:P -'X) = f.

(** Prove this equation by induction on [i].
Hint: relevant lemmas are scale* mulr* addr* expr* oppr* in ssralg,
derivnS derivZ deriv_comp derivE in poly *)
Lemma  derivn_fpix: forall i , (f^`(i)\Po(pi%:P -'X))= (-1)^+i *: f^`(i).
Proof.
(*X*)elim ; first by rewrite /= expr0 scale1r pf_sym.
(*X*)move => i Hi.
(*X*)set fx := _ \Po _.
(*X*)rewrite derivnS exprS -scalerA -derivZ -Hi deriv_comp !derivE.
(*X*)by rewrite mulrBr mulr0 add0r mulr1 -derivnS /fx scaleN1r opprK.
(*A*)Qed.

(** Prove that F at pi is a Qint.
Hint: relevant lemmas are horner_comp sqrr_sign mulnC scale1r *)
Lemma FPi_int : F.[pi] \is a Qint.
Proof.
(*X*)rewrite /F horner_sum rpred_sum //.
(*X*)move=> i _ ; rewrite !hornerE rpredM //.
(*X*)  by rewrite -exprnP rpredX.
(*X*)move:(derivn_fpix (2*i)).
(*X*)rewrite  mulnC exprM sqrr_sign scale1r => <-.
(*X*)by rewrite horner_comp !hornerE subrr derive_f_0_int.
(*A*)Qed.

End Polynomes.

(*X*)(* 
(*X*)*** Local Variables: ***
(*X*)*** coq-prog-args: ("-emacs-U" "-R" "/Users/lrg/coq/math-comp/mathcomp" "mathcomp" "-I" "/Users/lrg/coq/math-comp/mathcomp" ) ***
(*X*)*** End: ***
(*X*)*)

