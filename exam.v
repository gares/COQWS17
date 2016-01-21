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


From mathcomp Require Import all_algebra.
From mathcomp Require Import algC.

Section AlgebraicHierarchy.
Section GaussIntegers.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition gaussInteger := [qualify a x | ('Re x \in Cint) && ('Im x \in Cint)].
Axiom Cint_GI : forall (x : algC), x \in Cint -> x \is a gaussInteger.
Axiom GI_subring : subring_closed gaussInteger.

Fact GI_key : pred_key gaussInteger. Proof. by []. Qed.
Canonical GI_keyed := KeyedQualifier GI_key.
Canonical GI_opprPred := OpprPred GI_subring.
Canonical GI_addrPred := AddrPred GI_subring.
Canonical GI_mulrPred := MulrPred GI_subring.
Canonical GI_zmodPred := ZmodPred GI_subring.
Canonical GI_semiringPred := SemiringPred GI_subring.
Canonical GI_smulrPred := SmulrPred GI_subring.
Canonical GI_subringPred := SubringPred GI_subring.

Record GI := GIof {algGI : algC; algGIP : algGI \is a gaussInteger }.
Hint Resolve algGIP.

Canonical GI_subType := [subType for algGI].
Definition GI_eqMixin := [eqMixin of GI by <:].
Canonical GI_eqType := EqType GI GI_eqMixin.
Definition GI_choiceMixin := [choiceMixin of GI by <:].
Canonical GI_choiceType := ChoiceType GI GI_choiceMixin.
Definition GI_countMixin := [countMixin of GI by <:].
Canonical GI_countType := CountType GI GI_countMixin.
Definition GI_zmodMixin := [zmodMixin of GI by <:].
Canonical GI_zmodType := ZmodType GI GI_zmodMixin.
Definition GI_ringMixin := [ringMixin of GI by <:].
Canonical GI_ringType := RingType GI GI_ringMixin.
Definition GI_comRingMixin := [comRingMixin of GI by <:].
Canonical GI_comRingType := ComRingType GI GI_comRingMixin.

Lemma conjGIE x : (x^* \is a gaussInteger) = (x \is a gaussInteger).
Proof. by rewrite ![_ \is a _]qualifE algRe_conj algIm_conj rpredN. Qed.

Fact conjGI_subproof (x : GI) : (val x)^* \is a gaussInteger.
Proof. by rewrite conjGIE. Qed.

Canonical conjGI x := GIof (conjGI_subproof x).

Definition gaussNorm (x : algC) := x * x^*.

Axiom gaussNormE : forall x, gaussNorm x = `|x| ^+ 2.
Axiom gaussNormCnat : forall (x : GI), gaussNorm (val x) \in Cnat.

Lemma gaussNorm1 : gaussNorm 1 = 1.
(*A*)Proof. by rewrite /gaussNorm rmorph1 mulr1. Qed.

Lemma gaussNormM : {morph gaussNorm : x y / x * y}.
(*A*)Proof. by move=> x y; rewrite /gaussNorm rmorphM mulrACA. Qed.
(**

** Question: Prove that GI euclidean for the stasm gaussNorm.

 - i.e. ∀ (a, b) ∈ GI × GI*, ∃ (q, r) ∈ GI² s.t. a = q b + r and φ(r) < φ(b)
 - Suggested strategy: sketch the proof on a paper first, don't let Coq
   divert you from your proofsketch
 - We first sketch the "paper proof" here and then do it in Coq:
  - take a / b = x + i y
  - take u the closest integer to x, and v the closest integer to y
  - satisfy the existential with q = u + i v and r = a - q b, 
    which are both Gauss integers.
  - We want to show that |a - q b|² < |b|².
  - It suffices to show |a / b - q|² < 1
  - But |a / b - q|² = (u - x)² + (v - x)² ≤ ‌½² + ½² < 1
 - Now we give a Coq proof with holes, fill in the holes.
*)
Lemma euclideanGI (a b : GI) : b != 0 ->
  exists2 qr : GI * GI, a = qr.1 * b + qr.2
                      & (gaussNorm (val qr.2) < gaussNorm (val b)).
Proof.
move=> b_neq0.

(* Trivial preliminaries *)
have oneV2 : 1 = 2%:R^-1 + 2%:R^-1 :> algC.
  by rewrite -mulr2n -[_ *+ 2]mulr_natr mulVf ?pnatr_eq0.
have V2ge0 : 0 <= 2%:R^-1 :> algC by (*a*)rewrite invr_ge0 ler0n.
have V2real : (2%:R^-1 : algC) \is Num.real by (*a*)rewrite realE V2ge0.

(* Closest integer to x, when x is real *)
pose approx (x : algC) : int :=
  floorC x + (if `|x - (floorC x)%:~R| <= 2%:R^-1 then 0 else 1).
have approxP x : x \is Creal -> `|x - (approx x)%:~R| <= 2%:R^-1.
  rewrite /approx => x_real; have /andP [x_ge x_le] := floorC_itv x_real.
  have [] // := @real_lerP _  `|_ - (floorC _)%:~R| _;
    first by rewrite addr0.
  rewrite [`|_ - (_ + 1)%:~R|]distrC !ger0_norm ?subr_ge0 //=;
     last by rewrite ltrW.
  move=> Dx1_gtV2; rewrite real_lerNgt ?rpredB // ?Creal_Cint ?Cint_int //.
  apply/negP=> /ltr_add /(_ Dx1_gtV2); rewrite -oneV2 !addrA addrNK.
  by rewrite [_ + 1]addrC rmorphD /= addrK ltrr.
have approxP2 x (_ : x \is Creal) : `|x - (approx x)%:~R| ^+ 2 < 2%:R^-1.
  rewrite (@ler_lt_trans _ (2%:R^-1 ^+ 2)) // ?ler_expn2r ?qualifE ?approxP //.
  by rewrite exprVn -natrX ltf_pinv ?qualifE ?ltr_nat ?ltr0n.

(* Proper proof *)
pose u := 'Re (val a / val b); pose v := 'Im (val a / val b).
have qGI : (approx u)%:~R + algCi * (approx v)%:~R \is a gaussInteger.
(*a*)  by rewrite qualifE /= algRe_rect ?algIm_rect // ?Creal_Cint ?Cint_int.
pose q := GIof qGI.
exists (q, a - q * b); first by rewrite addrC addrNK.
rewrite !gaussNormE /=.
rewrite -(@ltr_pmul2r _ (`|val b| ^-2)) ?invr_gt0 ?exprn_gt0 ?normr_gt0 //.
rewrite mulfV ?expf_eq0 /= ?normr_eq0 // -exprVn -exprMn.
rewrite -normfV -normrM mulrBl mulfK //.
(*X*)rewrite [X in X - _]algCrect opprD addrACA -mulrBr -/u -/v.
set Du := _ - _; set Dv := _ - _.
have /andP [DuReal DvReal] : (Du \is Creal) && (Dv \is Creal).
(*a*)  by rewrite ?rpredB ?Creal_Re ?Creal_Im ?Creal_Cint ?Cint_int.
(*X*)rewrite normC2_rect // -real_normK // -[Dv ^+ _]real_normK //.
(*X*)by rewrite oneV2 ltr_add // approxP2 // ?Creal_Re ?Creal_Im.
(*A*)Qed.

End GaussIntegers.
End AlgebraicHierarchy.

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

Section LinearAlgebra.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
(**

* Endomorphisms u such that Ker u ⊕ Im u = E.

The endomorphisms of a space E of finite dimension n, such that u o v
= 0 and v + u is invertible are exactly the endomorphisms such that
Ker u ⊕ Im u = E.

 - Assume u o v = 0 and v + u is invertible,
  - we have rank (v + u) = n
  - we rank v + rank u = n and we have Im v ⊂ Ker u
  - Hence we have Im v = Ker u
  - We deduce that Ker u ⊕ Im u = Im v ⊕ Im u = E
*)
Variables (F : fieldType) (n' : nat).
Let n := n'.+1.

Lemma ex_6_13 (u : 'M[F]_n):
  reflect (exists2 v : 'M_n, v * u = 0 & v + u \is a GRing.unit)
          ((kermx u + u == 1)%MS && mxdirect (kermx u + u)).
Proof.
apply: (iffP idP) => [|[v vMu vDu]]; last first.
  have rkvDu: \rank (v + u)%R = n by (*a*)rewrite mxrank_unit.
  have /eqP rkvDrku : (\rank v + \rank u)%N == n.
    by rewrite eqn_leq (*a*)mulmx0_rank_max //= -{1}rkvDu mxrank_add //.
  have sub_v_ku : (v <= kermx u)%MS by (*a*)apply/sub_kermxP.
  have /eqmxP/eqmx_sym eq_vu: (v == kermx u)%MS.
    rewrite -(geq_leqif (mxrank_leqif_eq _)) //.
(*X*)    rewrite -(leq_add2r (\rank u)) rkvDrku.
    (*a*)by rewrite mxrank_ker subnK // rank_leq_row.
  rewrite submx1 sub1mx -col_leq_rank mxdirectEgeq /=.
  (* use addx_eqmx to lift eq_vu to a sum *)
(*X*)  rewrite eq_vu (adds_eqmx eq_vu (eqmx_refl _)).
  (* Warning: - (u + v)%R  is a sum of matrices
              - (u + v)%MS is a sum of spaces
     use addmx_sub_adds and mxrankS
     to compare the rank (u + v) with dim (Im u + Im v) *)
(*X*)  have /mxrankS leq_rk := addmx_sub_adds (submx_refl v) (submx_refl u).
  (* finish using hypothesis *)
  (*a*)by rewrite !(leq_trans _ leq_rk) //= ?rkvDu ?rkvDrku.
move=> /andP [/eqmxP kuDu_eq1 kvDu_direct].
pose v := proj_mx (kermx u) u; exists v.
  (*a*)by apply/sub_kermxP; rewrite -[X in (X <= _)%MS]mul1r proj_mx_sub.
rewrite -row_free_unit -kermx_eq0.
apply/negP => /negP /rowV0Pn [x /sub_kermxP]; rewrite mulmxDr.
move=> /(canRL (addrK _)); rewrite sub0r => eq_xv_Nxu.
apply/negP; rewrite negbK; apply/eqP.
have : (x *m v <= kermx u :&: u)%MS.
  (*a*)by rewrite sub_capmx proj_mx_sub eq_xv_Nxu eqmx_opp submxMl.
(*X*)rewrite (mxdirect_addsP _) ?submx0 // => /eqP xv_eq0.
(*X*)move/eqP : eq_xv_Nxu; rewrite xv_eq0 eq_sym oppr_eq0 => /eqP.
(*X*)move=> /sub_kermxP x_in_keru; move: xv_eq0; rewrite proj_mx_id //.
(*X*)by rewrite (mxdirect_addsP _).
(*A*)Qed.

End LinearAlgebra.

(*X*)(* 
(*X*)*** Local Variables: ***
(*X*)*** coq-prog-args: ("-emacs-U" "-R" "/Users/lrg/coq/math-comp/mathcomp" "mathcomp" "-I" "/Users/lrg/coq/math-comp/mathcomp" ) ***
(*X*)*** End: ***
(*X*)*)

