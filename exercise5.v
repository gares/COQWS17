From mathcomp Require Import all_ssreflect all_algebra all_field.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Let's do some CPGE exercices :) *)

Section GaussIntegers.
(* Ring of Gauss integer *)
(* Ref: exercices de mathematiques oraux X-ENS algebre 1 *)
(* Exercice 3.10 *)

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(* Notions:
- boolean predicates various definition and use
*)
Definition gaussInteger := [qualify a x | ('Re x \in Cint) && ('Im x \in Cint)].

Lemma GIRe x : x \is a gaussInteger -> 'Re x \in Cint.
Proof. by move=> /andP[]. Qed.
Lemma GIIm x : x \is a gaussInteger -> 'Im x \in Cint.
Proof. by move=> /andP[]. Qed.

Lemma algReM x y : 'Re (x * y) = 'Re x * 'Re y - 'Im x * 'Im y.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect algRe_rect //.
  by rewrite rpredB // rpredM // ?Creal_Re ?Creal_Im.
by rewrite rpredD // rpredM // ?Creal_Re ?Creal_Im.
Qed.

Lemma algImM x y : 'Im (x * y) = 'Re x * 'Im y + 'Re y * 'Im x.
Proof.
rewrite {1}[x]algCrect {1}[y]algCrect mulC_rect algIm_rect //.
  by rewrite rpredB // rpredM // ?Creal_Re ?Creal_Im.
by rewrite rpredD // rpredM // ?Creal_Re ?Creal_Im.
Qed.

Lemma GI_subring : subring_closed gaussInteger.
Proof.
split => [|x y xGI yGI|x y xGI yGI].
- by rewrite qualifE (Creal_ReP _ _) ?(Creal_ImP _ _) // rpred1 rpred0.
- by rewrite qualifE !raddfB /= ?(rpredB, GIRe, GIIm).
by rewrite qualifE algReM algImM rpredB ?rpredD // rpredM ?GIRe ?GIIm.
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

Lemma gaussNormCnat x : x \is a gaussInteger -> gaussNorm x \in Cnat.
Proof.
rewrite qualifE /gaussNorm => /andP [ReInt ImInt].
by rewrite -normCK normC2_Re_Im rpredD // Cnat_exp_even.
Qed.

Lemma conjGI x : (x^* \is a gaussInteger) = (x \is a gaussInteger).
Proof. by rewrite ![_ \is a _]qualifE algRe_conj algIm_conj rpredN. Qed.

Definition unitGI : pred_class :=
  [pred x : algC | (x != 0) && (x^-1 \is a gaussInteger)].

Fact muleq1_eq0 (R : ringType) (x y : R) : x * y = 1 -> x != 0.
Proof. by apply: contra_eqN => /eqP ->; rewrite mul0r eq_sym oner_eq0. Qed.

Fact muleq1_unit (R : comUnitRingType) (x y : R) : x * y = 1 -> x \is a GRing.unit.
Proof. by move=> xy_eq1; apply/unitrP; exists y; split=> //; rewrite mulrC. Qed.

Fact muleq1VE (R : comUnitRingType) (x y : R) : x * y = 1 -> x = y^-1.
Proof.
move=> /(fun x => (x, x)) [/muleq1_unit x_unit].
by move=> /(canRL (mulKr x_unit)) ->; rewrite mulr1 invrK.
Qed.

Fact muleq1_VEAneq0 (R : comUnitRingType) (x y : R) : x * y = 1 -> 
 [/\ x != 0, y != 0 & x = y^-1].
Proof. 
move=> xy_eq1; split; [apply: muleq1_eq0 xy_eq1| |apply: muleq1VE] => //.
by move: xy_eq1; rewrite mulrC => /muleq1_eq0.
Qed.

Lemma unitGIP (x : algC) :
  reflect (exists2 y, y \is a gaussInteger & x * y = 1) (x \in unitGI).
Proof.
apply: (iffP andP) => [[xU xVGI]|[y yGI /muleq1_VEAneq0 [? ? ->]]].
  by exists x^-1; rewrite // divff //= -unitfE.
by rewrite invrK invr_eq0.
Qed.

(* Notions: unitfE, eqVneq *)
Lemma unitGIE x : x \is a gaussInteger -> (x \in unitGI) = (gaussNorm x == 1).
Proof.
move=> xGI; apply/unitGIP/eqP; last first.
  move=> /muleq1_VEAneq0 [? ? ->]; exists x^*; rewrite ?mulVr ?unitfE //.
  by rewrite conjGI.
move=> [y yGI] /(congr1 gaussNorm); rewrite gaussNormM gaussNorm1.
have /CnatP [n ->] := gaussNormCnat xGI.
have /CnatP [m ->] := gaussNormCnat yGI.
by move=> /eqP; rewrite -natrM pnatr_eq1 muln_eq1 => /andP[/eqP -> _].
Qed.

(* *)
Lemma euclideanGI (a b : algC) : b != 0 ->
  a \is a gaussInteger -> b \is a gaussInteger ->
  exists2 qr : algC * algC, (qr.1 \is a gaussInteger) && (qr.2 \is a gaussInteger)
                                                      && (gaussNorm qr.2 < gaussNorm b)
                            & a = b * qr.1 + qr.2.
Proof.
move=> b_neq0 aGI bGI.
pose approx (x : algC) := floorC x +
                          (if `|(floorC x)%:~R - x| <= 2%:R^-1 then 0 else 1).
have approx_leq x : `|(approx x)%:~R - x| <= 2%:R^-1.
  admit.
pose u := 'Re (a / b); pose v := 'Im (a / b).
pose q := (approx u)%:~R + algCi * (approx v)%:~R.
have qGI : q \is a gaussInteger.
  by rewrite qualifE /q /= algRe_rect ?algIm_rect // ?Creal_Cint ?Cint_int.
exists (q, a - b * q) => /=; last by rewrite addrC addrNK.
rewrite qGI /= !gaussNormE rpredB ?rpredM //=.
rewrite -(@ltr_pmul2r _ (`|b| ^-2)) ?invr_gt0 ?exprn_gt0 ?normr_gt0 //.
rewrite divff ?expf_eq0 /= ?normr_eq0 //.
rewrite -exprVn -exprMn.
  
  

(* End of exercices *)


