From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory UnityRootTheory.
Open Scope ring_scope.

Section PreliminaryLemmas.
(**
* Preliminaries

Let's extend the library on rings and algebraic numbers
with some easy lemmas first.

** Question -2: prove that if a product of natural numbers is 1 then each factor is 1.

Note that we do not consider nat but the copy of nat which is embeded
in the algebraic numbers algC. The theorem already exists for nat, and
we suggest you use a compatibility lemma numbers between nat and Cnat
*)
Lemma Cnat_mul_eq1 : {in Cnat &, forall x y, (x * y == 1) = (x == 1) && (y == 1)}.
Proof.
(*D*)by move=> x y /CnatP [n ->] /CnatP [m ->]; rewrite -natrM !pnatr_eq1 muln_eq1.
(*A*)Qed.

Lemma Cnat_add_eq1 : {in Cnat &, forall x y,
   (x + y == 1) = ((x == 1) && (y == 0)) || ((x == 0) && (y == 1))}.
Proof.
(*D*)move=> x y /CnatP [n ->] /CnatP [m ->]; rewrite -natrD !pnatr_eq1 ?pnatr_eq0.
(*D*)by move: n m => [|[|?]] [|[|?]].
(*A*)Qed.
(**
** Question -1: The real part of product
*)
Lemma algReM (x y : algC) : 
  'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof.
(*D*)rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect algRe_rect //;
(*D*)by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
(*A*)Qed.
(**
** Question 0: The imaginary part of product
*)
Lemma algImM (x y : algC) : 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
(*D*)rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect algIm_rect //;
(*D*)by rewrite rpredD ?rpredN // rpredM // ?Creal_Re ?Creal_Im.
(*A*)Qed.

End PreliminaryLemmas.
(**
----
* The ring of Gauss integers

 - Ref: exercices de mathematiques oraux X-ENS algebre 1
 - Exercice 3.10. ENS Lyon

*)
Section GaussIntegers.
(**
First we define a predicate for the algebraic numbers which are gauss integers.
*)
Definition gaussInteger := [qualify a x | ('Re x \in Cint) && ('Im x \in Cint)].
(**

** Question 1: Prove that integers are gauss integers

*)
Lemma Cint_GI (x : algC) : x \in Cint -> x \is a gaussInteger.
Proof.
(*D*)move=> x_int; rewrite qualifE (Creal_ReP _ _) ?(Creal_ImP _ _) ?Creal_Cint //.
(*D*)by rewrite x_int rpred0.
(*A*)Qed.
(**

** Question 2: Prove that gauss integers form a subfield
*)
Lemma GI_subring : subring_closed gaussInteger.
Proof.
(*D*)split => [|x y /andP[??] /andP[??]|x y /andP[??] /andP[??]].
(*D*)- by rewrite Cint_GI.
(*D*)- by rewrite qualifE !raddfB /= ?rpredB.
(*D*)by rewrite qualifE algReM algImM rpredB ?rpredD // rpredM.
(*A*)Qed.
(**

There follows the boilerplate to use the proof GI_subring in order to
canonically provide a subring structure to the predicate gaussInteger.

*)
Fact GI_key : pred_key gaussInteger. Proof. by []. Qed.
Canonical GI_keyed := KeyedQualifier GI_key.
Canonical GI_opprPred := OpprPred GI_subring.
Canonical GI_addrPred := AddrPred GI_subring.
Canonical GI_mulrPred := MulrPred GI_subring.
Canonical GI_zmodPred := ZmodPred GI_subring.
Canonical GI_semiringPred := SemiringPred GI_subring.
Canonical GI_smulrPred := SmulrPred GI_subring.
Canonical GI_subringPred := SubringPred GI_subring.
(**

Finally, we define the type of Gauss Integer, as a sigma type of
algebraic numbers. We soon prove that this is in fact a sub type.

*)
Record GI := GIof {
  algGI : algC;
  algGIP : algGI \is a gaussInteger }.
(** We make the defining property of GI a Hint *)
Hint Resolve algGIP.
(**

We provide the subtype property.

- This makes it possible to use the generic operator "val" to get an
  algC from a Gauss Integer.

*)
Canonical GI_subType := [subType for algGI].
(**
We deduce that the real and imaginary parts of a GI are integers
*)
Lemma GIRe (x : GI) : 'Re (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Lemma GIIm (x : GI) : 'Im (val x) \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Hint Resolve GIRe GIIm.

Canonical ReGI x := GIof (Cint_GI (GIRe x)).
Canonical ImGI x := GIof (Cint_GI (GIIm x)).
(**

We provide a ring structure to the type GI, using the subring
canonical property for the predicate gaussInteger

*)
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
(* Definition GI_unitRingMixin := [unitRingMixin of GI by <:]. *)
(* Canonical GI_unitRingType := UnitRingType GI GI_unitRingMixin. *)
(**

 - Now we build the unitRing and comUnitRing structure of gauss
   integers. Contrarily to the previous structures, the operator is
   not the same as on algebraics. Indeed the invertible algebraics are
   not necessarily invertible gauss integers.

 - Hence, we define the inverse of gauss integers as follow : if the
   algebraic inverse happens to be a gauss integer we recover the
   proof and package it together with the element and get a gauss
   integer, otherwise, we default to the identity.

 - A gauss integer is invertible if the algbraic inverse is a gauss
   integer.

*)
Definition invGI (x : GI) := insubd x (val x)^-1.
Definition unitGI (x : GI) :=
  (x != 0) && ((val x)^-1 \is a gaussInteger).
(**

** Question 3: prove a few facts in order to find a comUnitRingMixin
for GI, and then instantiate the interfaces of unitRingType and
comUnitRingType.


*)
(*D*)Fact mulGIr : {in unitGI, left_inverse 1 invGI *%R}.
(*D*)Proof.
(*D*)move=> x /andP [x_neq0 xVGI]; rewrite /invGI.
(*D*)by apply: val_inj; rewrite /= insubdK // mulVr ?unitfE.
(*D*)Qed.
(*D*)
(*D*)Fact unitGIP (x y : GI) : y * x = 1 -> unitGI x.
(*D*)Proof.
(*D*)rewrite /unitGI => /(congr1 val) /=.
(*D*)have [-> /eqP|x_neq0] := altP (x =P 0); first by rewrite mulr0 eq_sym oner_eq0.
(*D*)by move=> /(canRL (mulfK x_neq0)); rewrite mul1r => <- /=.
(*D*)Qed.
(*D*)
(*D*)Fact unitGI_out : {in [predC unitGI], invGI =1 id}.
(*D*)Proof.
(*D*)move=> x; rewrite inE /= -topredE /= /unitGI.
(*D*)rewrite negb_and negbK => /predU1P [->|/negPf xGIF];
(*D*)by apply: val_inj; rewrite /invGI ?val_insubd /= ?xGIF // invr0 if_same.
(*D*)Qed.
(*D*)
Definition GI_comUnitRingMixin :=
(*D*)  ComUnitRingMixin mulGIr unitGIP unitGI_out.
Canonical GI_unitRingType := UnitRingType GI GI_comUnitRingMixin.
Canonical GI_comUnitRingType := [comUnitRingType of GI].
(**

** Question 4: Show that gauss integers are stable by conjugation.

*)
Lemma conjGIE x : (x^* \is a gaussInteger) = (x \is a gaussInteger).
(*A*)Proof. by rewrite ![_ \is a _]qualifE algRe_conj algIm_conj rpredN. Qed.
(**

We use this fact to build the conjugation of a gauss Integers

*)
Fact conjGI_subproof (x : GI) : (val x)^* \is a gaussInteger.
Proof. by rewrite conjGIE. Qed.

Canonical conjGI x := GIof (conjGI_subproof x).
(**

We now define the norm (stasm) for gauss integer, we don't need to
specialize it to gauss integer so we define it over algebraic numbers
instead.

*)
Definition gaussNorm (x : algC) := x * x^*.
(**

** Question 4: Show that the gaussNorm of x is the square of the complex modulus of x

*)
Lemma gaussNormE x : gaussNorm x = `|x| ^+ 2.
(*A*)Proof. by rewrite normCK. Qed.
(**

** Question 5: Show that the gaussNorm of an gauss integer is a natural number.

*)
Lemma gaussNormCnat (x : GI) : gaussNorm (val x) \in Cnat.
(*A*)Proof. by rewrite /gaussNorm -normCK normC2_Re_Im rpredD // Cnat_exp_even. Qed.
Hint Resolve gaussNormCnat.
(**

** Question 6: Show that gaussNorm is multiplicative (on all algC).

*)
Lemma gaussNorm1 : gaussNorm 1 = 1.
(*A*)Proof. by rewrite /gaussNorm rmorph1 mulr1. Qed.

Lemma gaussNormM : {morph gaussNorm : x y / x * y}.
(*A*)Proof. by move=> x y; rewrite /gaussNorm rmorphM mulrACA. Qed.
(**

** Question 7: Find the invertible elements of GI

 - This is question 1 of the CPGE exercice

 - Suggested strategy: sketch the proof on a paper first, don't let
   Coq divert you from your proofsketch

*)
Lemma unitGIE (x : GI) : (x \in GRing.unit) =
(*D*) (val x \in 4.-unity_root).
(*D*)Proof.
(*D*)have eq_algC a b : (a == b) = ('Re a == 'Re b) && ('Im a == 'Im b).
(*D*)  rewrite {1}[a]algCrect {1}[b]algCrect -subr_eq0 opprD addrACA -mulrBr.
(*D*)  rewrite -normr_eq0 -sqrf_eq0 normC2_rect ?rpredB ?Creal_Re ?Creal_Im //.
(*D*)  rewrite paddr_eq0 ?real_exprn_even_ge0 // ?rpredB ?Creal_Re ?Creal_Im //.
(*D*)  by rewrite !expf_eq0 /= !subr_eq0.
(*D*)have N1Creal : -1 \is Creal by rewrite rpredN.
(*D*)have oneE :    1 = 1 + 'i * 0     by rewrite mulr0 addr0.
(*D*)have N1E  :  - 1 = - 1 + 'i * 0   by rewrite mulr0 addr0.
(*D*)have iE   :   'i = 0 + 'i * 1     by rewrite mulr1 add0r.
(*D*)have NiE  : - 'i = 0 + 'i * (- 1) by rewrite mulrN1 add0r.
(*D*)have onerN1 : (1 == -1 :> algC) = false.
(*D*)  by rewrite -subr_eq0 opprK paddr_eq0 ?oner_eq0 ?ler01.
(*D*)pose my := @id algC.
(*D*)transitivity (gaussNorm (val x) == 1).
(*D*)  apply/idP/eqP; last first.
(*D*)    by move=> gNx; apply/unitrPr; exists (conjGI x); apply: val_inj.
(*D*)  move=> x_unit; have /(congr1 (gaussNorm \o val)) /= /eqP := mulrV x_unit.
(*D*)  by rewrite gaussNormM gaussNorm1 Cnat_mul_eq1 //= => /andP [/eqP].
(*D*)rewrite (@mem_unity_roots _ 4 (map my [:: 1; -1; 'i; -'i])) //; last 2 first.
(*D*)- rewrite /= !unity_rootE /= [(- 'i) ^+ _]exprNn expr1n  -signr_odd ?expr0.
(*D*)  by rewrite -[4]/(2 * 2)%N exprM sqrCi -signr_odd ?expr0 mulr1 !eqxx.
(*D*)- rewrite /= ![my _](iE, oneE, N1E, NiE).
(*D*)  rewrite /= !in_cons !in_nil /= !negb_or -!andbA !andbT /=.
(*D*)  rewrite ![_ + 'i * _ == _]eq_algC ?algRe_rect ?algIm_rect //.
(*D*)  rewrite ![_ == -1]eq_sym ![_ == 1]eq_sym oppr_eq0.
(*D*)  by rewrite eqxx onerN1 oner_eq0.
(*D*)rewrite gaussNormE [val x]algCrect normC2_rect ?Creal_Re ?Creal_Im //.
(*D*)rewrite Cnat_add_eq1 ?Cnat_exp_even ?expf_eq0 //=.
(*D*)rewrite -Cint_normK // -Cint_normK //.
(*D*)rewrite !expr2 !Cnat_mul_eq1 ?andbb ?Cnat_norm_Cint //.
(*D*)rewrite !real_eqr_norml ?Creal_Re ?Creal_Im ?ler01 ?andbT //=.
(*D*)rewrite !inE ![my _](iE, oneE, N1E, NiE).
(*D*)rewrite ![_ + 'i * _ == _]eq_algC
(*D*)   ?algRe_rect ?algIm_rect // ?Creal_Re ?Creal_Im //.
(*D*)by rewrite andb_orl andb_orr -orbA.
(*A*)Qed.
(**

** Question 8: Prove that GI euclidean for the stasm gaussNorm.

 - i.e. ∀ (a, b) ∈ GI × GI*, ∃ (q, r) ∈ GI² s.t. a = q b + r and φ(r) < φ(b)
 - This is question 2 of the CPGE exercice
 - Suggested strategy: sketch the proof on a paper first, don't let Coq
   divert you from your proofsketch

*)
Lemma euclideanGI (a b : GI) : b != 0 ->
  exists2 qr : GI * GI, a = qr.1 * b + qr.2
                      & (gaussNorm (val qr.2) < gaussNorm (val b)).
Proof.
move=> b_neq0.
(*D*)have oneV2 : 1 = 2%:R^-1 + 2%:R^-1 :> algC.
(*D*)  by rewrite -mulr2n -[_ *+ 2]mulr_natr mulVf ?pnatr_eq0.
(*D*)have V2ge0 : 0 <= 2%:R^-1 :> algC by rewrite invr_ge0 ler0n.
(*D*)have V2real : 2%:R^-1 \is Creal by rewrite realE V2ge0.
pose approx (x : algC) : int :=
(*D*)  floorC x + (if `|x - (floorC x)%:~R| <= 2%:R^-1 then 0 else 1).
have approxP x : x \is Creal -> `|x - (approx x)%:~R| <= 2%:R^-1.
(*D*)  rewrite /approx => x_real; have /andP [x_ge x_le] := floorC_itv x_real.
(*D*)  have [] // := @real_lerP _  `|_ - (floorC _)%:~R| _;
(*D*)  first by rewrite addr0.
(*D*)  rewrite [`|_ - (_ + 1)%:~R|]distrC !ger0_norm ?subr_ge0 //=;
(*D*)     last by rewrite ltrW.
(*D*)  move=> Dx1_gtV2; rewrite real_lerNgt ?rpredB // ?Creal_Cint ?Cint_int //.
(*D*)  apply/negP=> /ltr_add /(_ Dx1_gtV2); rewrite -oneV2 !addrA addrNK.
(*a*)  by rewrite [_ + 1]addrC rmorphD /= addrK ltrr.
(*D*)have approxP2 x (_ : x \is Creal) : `|x - (approx x)%:~R| ^+ 2 < 2%:R^-1.
(*D*)  rewrite (@ler_lt_trans _ (2%:R^-1 ^+ 2)) // ?ler_expn2r ?qualifE ?approxP //.
(*D*)  by rewrite exprVn -natrX ltf_pinv ?qualifE ?ltr_nat ?ltr0n.
(*D*)pose u := 'Re (val a / val b); pose v := 'Im (val a / val b).
(*D*)have qGI : (approx u)%:~R + algCi * (approx v)%:~R \is a gaussInteger.
(*D*)  by rewrite qualifE /= algRe_rect ?algIm_rect // ?Creal_Cint ?Cint_int.
(*D*)pose q := GIof qGI.
(*D*)exists (q, a - q * b); first by rewrite addrC addrNK.
(*D*)rewrite !gaussNormE /=.
(*D*)rewrite -(@ltr_pmul2r _ (`|val b| ^-2)) ?invr_gt0 ?exprn_gt0 ?normr_gt0 //.
(*D*)rewrite mulfV ?expf_eq0 /= ?normr_eq0 // -exprVn -exprMn.
(*D*)rewrite -normfV -normrM mulrBl mulfK //.
(*D*)rewrite [X in X - _]algCrect opprD addrACA -mulrBr -/u -/v.
(*D*)set Du := _ - _; set Dv := _ - _.
(*D*)have /andP [DuReal DvReal] : (Du \is Creal) && (Dv \is Creal).
(*D*)   by rewrite ?rpredB ?Creal_Re ?Creal_Im ?Creal_Cint ?Cint_int.
(*D*)rewrite normC2_rect // -real_normK // -[Dv ^+ _]real_normK //.
(*D*)by rewrite oneV2 ltr_add // approxP2 // ?Creal_Re ?Creal_Im.
(*A*)Qed.

End GaussIntegers.
(* End of exercices *)
