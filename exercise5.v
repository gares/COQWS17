From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* Let's extend the library on rings with some easy lemmas *)

Section PreliminaryLemma.

Fact muleq1_eq0 (R : ringType) (x y : R) : x * y = 1 -> x != 0.
Proof. by apply: contra_eqN => /eqP ->; rewrite mul0r eq_sym oner_eq0. Qed.

Fact muleq1_unit (R : comUnitRingType) (x y : R) : x * y = 1 -> x \is a GRing.unit.
Proof. by move=> xy_eq1; apply/unitrP; exists y; split=> //; rewrite mulrC. Qed.

Fact muleq1VE (R : comUnitRingType) (x y : R) : x * y = 1 -> x = y^-1.
Proof.
move=> /(fun x => (x, x)) [/muleq1_unit x_unit].
by move=> /(canRL (mulKr x_unit)) ->; rewrite mulr1 invrK.
Qed.

Fact muleq1_neq0AV (R : comUnitRingType) (x y : R) : x * y = 1 -> 
 [/\ x != 0, y != 0 & x = y^-1].
Proof. 
move=> xy_eq1; split; [apply: muleq1_eq0 xy_eq1| |apply: muleq1VE] => //.
by move: xy_eq1; rewrite mulrC => /muleq1_eq0.
Qed.

Lemma algReM (x y : algC) : 'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect algRe_rect //.
  by rewrite rpredB // rpredM // ?Creal_Re ?Creal_Im.
by rewrite rpredD // rpredM // ?Creal_Re ?Creal_Im.
Qed.

Lemma algImM (x y : algC) : 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect algIm_rect //.
  by rewrite rpredB // rpredM // ?Creal_Re ?Creal_Im.
by rewrite rpredD // rpredM // ?Creal_Re ?Creal_Im.
Qed.

Lemma mulCnat_eq1 : {in Cnat &, forall x y, (x * y == 1) = (x == 1) && (y == 1)}.
Proof.
by move=> x y /CnatP [n ->] /CnatP [m ->]; rewrite -natrM !pnatr_eq1 muln_eq1.
Qed.

End PreliminaryLemma.

(** Let's do a CPGE exercice :) *)

Section GaussIntegers.
(* Ring of Gauss integer *)
(* Ref: exercices de mathematiques oraux X-ENS algebre 1 *)
(* Exercice 3.10. ENS Lyon *)

(* Notions:
- boolean predicates various definition and use
*)
Definition gaussInteger := [qualify a x | ('Re x \in Cint) && ('Im x \in Cint)].

Lemma Cint_GI (x : algC) : x \in Cint -> x \is a gaussInteger.
Proof.
move=> x_int; rewrite qualifE (Creal_ReP _ _) ?(Creal_ImP _ _) ?Creal_Cint //.
by rewrite x_int rpred0.
Qed.

Lemma GI_subring : subring_closed gaussInteger.
Proof.
split => [|x y /andP[??] /andP[??]|x y /andP[??] /andP[??]].
- by rewrite qualifE (Creal_ReP _ _) ?(Creal_ImP _ _) // rpred1 rpred0.
- by rewrite qualifE !raddfB /= ?rpredB.
by rewrite qualifE algReM algImM rpredB ?rpredD // rpredM.
Qed.

Fact GI_key : pred_key gaussInteger. Proof. by []. Qed.
Canonical GI_keyed := KeyedQualifier GI_key.

Canonical GI_opprPred := OpprPred GI_subring.
Canonical GI_addrPred := AddrPred GI_subring.
Canonical GI_mulrPred := MulrPred GI_subring.
Canonical GI_zmodPred := ZmodPred GI_subring.
Canonical GI_semiringPred := SemiringPred GI_subring.
Canonical GI_smulrPred := SmulrPred GI_subring.
Canonical GI_subringPred := SubringPred GI_subring.

Record GI := GIof {
 algGI :> algC;
 _ : algGI \is a gaussInteger
}.

Definition gi (x : GI) mkGI : GI :=
  mkGI (let: GIof _ giP := x return (x : algC) \is a gaussInteger in giP).

Notation "[ 'GI' 'of' x ]" := (gi (fun xP => @GIof x xP))
  (at level 0, format "[ 'GI'  'of'  x ]") : form_scope.

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

Lemma algGIP (x : GI) : (x : algC) \is a gaussInteger.
Proof. by case: x. Qed.
Hint Resolve algGIP.

Lemma GIRe (x : GI) : 'Re x \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Lemma GIIm (x : GI) : 'Im x \in Cint.
Proof. by have /andP [] := algGIP x. Qed.
Hint Resolve GIRe GIIm.

Canonical ReGI x := GIof (Cint_GI (GIRe x)).
Canonical ImGI x := GIof (Cint_GI (GIIm x)).

(* Notions: search lib algC *)
Definition gaussNorm (x : algC) := x * x^*.

Lemma gaussNormE x : gaussNorm x = `|x| ^+ 2.
Proof. by rewrite normCK. Qed.

(* Notions: rmorphism *)
Lemma gaussNorm1 : gaussNorm 1 = 1.
Proof. by rewrite /gaussNorm rmorph1 mulr1. Qed.

(* Notions: {morph ...} *)
Lemma gaussNormM : {morph gaussNorm : x y / x * y}.
Proof. by move=> x y; rewrite /gaussNorm rmorphM mulrACA. Qed.

Lemma gaussNormCnat (x : GI) : gaussNorm x \in Cnat.
Proof. by rewrite /gaussNorm -normCK normC2_Re_Im rpredD // Cnat_exp_even. Qed.
Hint Resolve gaussNormCnat.

Lemma conjGIE x : (x^* \is a gaussInteger) = (x \is a gaussInteger).
Proof. by rewrite ![_ \is a _]qualifE algRe_conj algIm_conj rpredN. Qed.

Fact conjGI_subproof (x : GI) : (x^* \is a gaussInteger).
Proof. by rewrite conjGIE. Qed.

Canonical conjGI x := GIof (conjGI_subproof x).

Definition invGI (x : GI) := insubd x (x : algC)^-1.
Definition unitGI (x : GI) := (x != 0) && ((x : algC)^-1 \is a gaussInteger).

Fact mulGIr : {in unitGI, left_inverse 1 invGI *%R}.
Proof.
move=> x /andP [x_neq0 xVGI]; rewrite /invGI.
by apply: val_inj; rewrite /= insubdK // mulVr ?unitfE.
Qed.

Fact unitGIP (x y : GI) : y * x = 1 -> unitGI x.
Proof.
move=> /(congr1 val) /= /muleq1_neq0AV [y_neq0 x_neq0 y_eq].
by rewrite /unitGI /= x_neq0 /= -y_eq.
Qed.

Fact out_unitGI : {in [predC unitGI], invGI =1 id}.
Proof.
move=> x; rewrite inE /= -topredE /= /unitGI.
rewrite negb_and negbK => /predU1P [->|/negPf xGIF];
by apply: val_inj; rewrite /invGI ?val_insubd /= ?xGIF // invr0 if_same.
Qed.

Definition GI_comUnitRingMixin := ComUnitRingMixin mulGIr unitGIP out_unitGI.
Canonical GI_unitRingType := UnitRingType GI GI_comUnitRingMixin.
Canonical GI_comUnitRingType := [comUnitRingType of GI].

(* Notions: unitfE, eqVneq *)
Lemma unitGIE (x : GI) : (x \in GRing.unit) = (gaussNorm x == 1).
Proof.
apply/idP/eqP; last first.
   by move=> gNx; apply/unitrPr; exists [GI of x^*]; apply: val_inj.
move=> x_unit; have /(congr1 (gaussNorm \o val)) /= /eqP := mulrV x_unit.
by rewrite gaussNormM gaussNorm1 mulCnat_eq1 //= => /andP [/eqP].
Qed.

(* *)
Lemma euclideanGI (a b : GI) : b != 0 ->
  exists2 qr : GI * GI, a = qr.1 * b + qr.2 & (gaussNorm qr.2 < gaussNorm b).
Proof.
have oneV2 : 1 = 2%:R^-1 + 2%:R^-1 :> algC.
  by rewrite -mulr2n -[_ *+ 2]mulr_natr mulVf ?pnatr_eq0.
move=> b_neq0; pose approx (x : algC) := floorC x +
  (if `|x - (floorC x)%:~R| <= 2%:R^-1 then 0 else 1).
have V2ge0 : 0 <= 2%:R^-1 :> algC by rewrite invr_ge0 ler0n.
have V2real : 2%:R^-1 \is Creal by rewrite realE V2ge0.
have approxP x : x \is Creal -> `|x - (approx x)%:~R| <= 2%:R^-1.
  rewrite /approx => x_real; have /andP [x_ge x_le] := floorC_itv x_real.
  have [] // := @real_lerP _  `|_ - (floorC _)%:~R| _; first by rewrite addr0.
  rewrite [`|_ - (_ + 1)%:~R|]distrC !ger0_norm ?subr_ge0 //=;
     last by rewrite ltrW.
  move=> Dx1_gtV2; rewrite real_lerNgt ?rpredB // ?Creal_Cint ?Cint_int //.
  apply/negP=> /ltr_add /(_ Dx1_gtV2); rewrite -oneV2 !addrA addrNK.
  by rewrite [_ + 1]addrC rmorphD /= addrK ltrr.
have approxP2 x (_ : x \is Creal) : `|x - (approx x)%:~R| ^+ 2 < 2%:R^-1.
  rewrite (@ler_lt_trans _ (2%:R^-1 ^+ 2)) // ?ler_expn2r ?qualifE ?approxP //.
  by rewrite exprVn -natrX ltf_pinv ?qualifE ?ltr_nat ?ltr0n.
pose u := 'Re ((a : algC) / (b : algC)); pose v := 'Im ((a : algC) / (b : algC)).
have qGI : (approx u)%:~R + algCi * (approx v)%:~R \is a gaussInteger.
  by rewrite qualifE /= algRe_rect ?algIm_rect // ?Creal_Cint ?Cint_int.
pose q := GIof qGI; exists (q, a - q * b); first by rewrite addrC addrNK.
rewrite !gaussNormE /=.
rewrite -(@ltr_pmul2r _ (`|b : algC| ^-2)) ?invr_gt0 ?exprn_gt0 ?normr_gt0 //.
rewrite mulfV ?expf_eq0 /= ?normr_eq0 // -exprVn -exprMn.
rewrite -normfV -normrM mulrBl mulfK //.
rewrite [X in X - _]algCrect opprD addrACA -mulrBr -/u -/v.
set Du := _ - _; set Dv := _ - _.
have /andP [DuReal DvReal] : (Du \is Creal) && (Dv \is Creal).
   by rewrite ?rpredB ?Creal_Re ?Creal_Im ?Creal_Cint ?Cint_int.
rewrite normC2_rect // -real_normK // -[Dv ^+ _]real_normK //.
by rewrite oneV2 ltr_add // approxP2 // ?Creal_Re ?Creal_Im.
Qed.

(* End of exercices *)


