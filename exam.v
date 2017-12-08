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
    in the code of [filtrev]?  Depending on how you expose
    the accumulator on the right hand side of the goal,
    such invariant may need to be taken into account by the induction.

Relevant keywords for [Search] are: rev cons cat filter rcons
Hint: it is perfectly fine to state intermediate lemmas
*)

Lemma filterrev_ok T p (l : seq T) :
  filtrev p [::] l = [seq x <- rev l | p x ].
Proof.
(*X*)rewrite -[RHS]cats0; elim: l [::] => [|x l ihl] l' //=.
(*X*)by case: ifP => px; rewrite ihl rev_cons filter_rcons ?px ?cat_rcons.
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
(*X*)rewrite (reindex_inj rev_ord_inj) /= => /negPf n_oddF.
(*X*)by apply: eq_big => i; rewrite odd_sub ?n_oddF //; case: n i {n_oddF}.
(*A*)Qed.

(** Even the Mathematical Components library misses some theorems,
    for example the following one.

    Would you help us improve the library with this lemma? 

    Hint: check out the theory of [iota]
*)

Lemma big_nat_shift (T : Type) (op: T -> T -> T) (idx : T)
  m c n (Pr : pred nat) (f : nat -> T):
  \big[op/idx]_(m + c <= i < n + c | Pr i) f i =
  \big[op/idx]_(m <= i < n | Pr (i + c)%N) f (i + c)%N.
Proof.
(*X*)rewrite [LHS](big_nth 0%N) [RHS](big_nth 0%N).
(*X*)rewrite !size_iota subnDr.
(*X*)rewrite [LHS]big_seq_cond [RHS]big_seq_cond.
(*X*)apply: eq_big.
(*X*)  move => i; rewrite mem_iota add0n subn0.
(*X*)  case h : (i < n - m)%N; last by rewrite andbF.
(*X*)  by rewrite !nth_iota // 1?addnAC // subnDr.
(*X*)move => i; rewrite mem_iota leq0n andTb add0n subn0 => /andP [] i_s _.
(*X*)by rewrite !nth_iota // ?subnDr 1?addnAC.
(*A*)Qed.

(**

Now, some algebra.

*)
From mathcomp Require Import all_algebra.
From mathcomp Require Import algC zmodp.

Section AlgebraicHierarchy.
Section GaussIntegers.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Big operations and [zmodType]. Now that [ring_scope] is open we are in
    an algebraic setting.  Think about the meaning of [+] now, and find
    the right injectivity lemma. *)
Lemma big_ord_shift1 (T : Type) (idx : T) (op : Monoid.com_law idx) n
 P F : \big[op/idx]_(i < n.+2 | P i) F i =
       \big[op/idx]_(i < n.+2 | P (i + 1)) F (i + 1).
Proof.
(*X*)apply: reindex_inj; apply: addIr.
(*A*)Qed.

(**

We remind what Gauss integer are and recall some theory about it.

*)
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
(**

Prove these two facts. (Hint: conjugation is a morphism)

*)
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
  (* Hint: use qualifE, alg*_rect and lemmas about Creal, Cint and _%:~R *)
  (*a*)by rewrite qualifE /= algRe_rect ?algIm_rect // ?Creal_Cint ?Cint_int.
pose q := GIof qGI.
exists (q, a - q * b); first by rewrite addrC addrNK.
rewrite !gaussNormE /=.
rewrite -(@ltr_pmul2r _ (`|val b| ^-2)) ?invr_gt0 ?exprn_gt0 ?normr_gt0 //.
rewrite mulfV ?expf_eq0 /= ?normr_eq0 // -exprVn -exprMn.
rewrite -normfV -normrM mulrBl mulfK //.
suff uvP : `|u - (approx u)%:~R + 'i * (v - (approx v)%:~R)| ^+ 2 < 1.
  (* Hint: use algCrect and algebraic transformations *)
  (*a*)by rewrite [X in X - _]algCrect opprD addrACA -mulrBr.
set Du := _ - _; set Dv := _ - _.
have /andP [DuReal DvReal] : (Du \is Creal) && (Dv \is Creal).
(* Hint: use rpred*, Creal_*, normC2_rect, ream_normK and approxP2 *)
(*a*)  by rewrite ?rpredB ?Creal_Re ?Creal_Im ?Creal_Cint ?Cint_int.
(*X*)rewrite normC2_rect // oneV2.
(*X*)by rewrite ltr_add // -real_normK // approxP2 ?Creal_Re ?Creal_Im.
(*A*)Qed.

End GaussIntegers.
End AlgebraicHierarchy.

Section PolynomialsLagrange.

Open Scope ring_scope.
Import GRing.Theory Num.Theory.
(**

* Definition and properties of Lagrange polynomials.

Prove only one of the following lemmas
*)
Variables (n : nat) (x : algC ^ n).

Definition lagrange (i : 'I_n) : {poly algC} :=
  let p := \prod_(j < n | j != i) ('X - (x j)%:P) in (p.[x i]^-1)%:P * p.

Hypothesis n_gt0 : (0 < n)%N.
Hypothesis x_inj : injective x.

Lemma lagrangeE (i j : 'I_n) : (lagrange i).[x j] = (i == j)%:R.
Proof using x_inj.
(*X*)rewrite /lagrange hornerM hornerC; set p := (\prod_(_ < _ | _) _).
(*X*)have [<-|neq_ij] /= := altP eqP.
(*X*)  rewrite mulVf // horner_prod; apply/prodf_neq0 => k neq_ki.
(*X*)  by rewrite hornerXsubC subr_eq0 inj_eq // eq_sym.
(*X*)rewrite [X in _ * X]horner_prod (bigD1 j) 1?eq_sym //=.
(*X*)by rewrite hornerXsubC subrr mul0r mulr0.
(*A*)Qed.


Lemma size_lagrange i : size (lagrange i) = n.
Proof using n_gt0 x_inj.
(*X*)rewrite size_Cmul; last first.
(*X*)  suff : (lagrange i).[x i] != 0 by rewrite hornerE mulf_eq0 => /norP [].
(*X*)  by rewrite lagrangeE ?eqxx ?oner_eq0.
(*X*)rewrite size_prod /=; last first.
(*X*)  by move=> j neq_ji; rewrite polyXsubC_eq0.
(*X*)rewrite (eq_bigr (fun=> (2 * 1)%N)); last first.
(*X*)  by move=> j neq_ji; rewrite size_XsubC.
(*X*)rewrite -big_distrr /= sum1_card cardC1 card_ord /=.
(*X*)by case: (n) {i} n_gt0 => ?; rewrite mul2n -addnn -addSn addnK.
(*A*)Qed.

Lemma lagrange_free (lambda : 'rV_n):
  \sum_i (lambda 0 i)%:P * lagrange i = 0 -> lambda = 0.
Proof using x_inj.
(*X*)move=> eq_l; apply/rowP=> i; rewrite mxE.
(*X*)have /(congr1 (fun p => p.[x i])) := eq_l.
(*X*)rewrite horner_sum horner0 (bigD1 i) //= hornerE lagrangeE // eqxx mulr1.
(*X*)rewrite big1 ?addr0 // => j neq_ji.
(*X*)by rewrite hornerM lagrangeE // (negPf neq_ji) mulr0.
(*A*)Qed.

Lemma lagrange_gen (p : {poly algC}) :
   (size p <= n)%N -> p = \sum_i p.[x i]%:P * lagrange i.
Proof using n_gt0 x_inj.
(*X*)(* fancy proof using marix spaces *)
(*X*)move=> sp_le_n; pose L := \matrix_(i < n) @poly_rV _ n (lagrange i).
(*X*)suff /(congr1 rVpoly) : poly_rV p = \row_i p.[x i] *m L.
(*X*)  rewrite poly_rV_K // => {1}->; rewrite mulmx_sum_row raddf_sum /=.
(*X*)  apply: eq_bigr=> i _; rewrite linearZ /= mxE mul_polyC.
(*X*)  by rewrite rowK poly_rV_K ?size_lagrange.
(*X*)have /submxP [u puL]: (poly_rV p <= L)%MS.
(*X*)  rewrite (submx_trans (submx1 _)) // sub1mx row_full_unit -row_free_unit.
(*X*)  rewrite -kermx_eq0; apply/rowV0P => v /sub_kermxP.
(*X*)  move=> /(congr1 rVpoly); rewrite !raddf0 mulmx_sum_row raddf_sum /= => vL0.
(*X*)  rewrite [v]lagrange_free // -[RHS]vL0; apply: eq_bigr => i _.
(*X*)  by rewrite linearZ rowK mul_polyC /= poly_rV_K ?size_lagrange.
(*X*)rewrite puL; congr (_ *m _); apply/rowP=> i; rewrite mxE.
(*X*)have /(congr1 (fun v => (rVpoly v).[x i])) := puL.
(*X*)rewrite poly_rV_K // mulmx_sum_row raddf_sum /=.
(*X*)rewrite (bigD1 i) //= linearZ /= rowK poly_rV_K ?size_lagrange //.
(*X*)rewrite 2!hornerE lagrangeE eqxx mulr1 horner_sum big1 ?addr0 //.
(*X*)move=> j neq_ji; rewrite linearZ rowK /= ?poly_rV_K ?size_lagrange //.
(*X*)by rewrite hornerZ lagrangeE (negPf neq_ji) mulr0.

(*X*)Restart. (* shorter proof, direct *)

(*X*)move=> sp_le_n; apply/eqP; rewrite -subr_eq0; apply: contraTT isT.
(*X*)move=> /max_poly_roots - /(_ [seq x i | i <- enum 'I_n]).
(*X*)rewrite size_map size_enum_ord map_inj_uniq ?enum_uniq //.
(*X*)rewrite [(n < _)%N]negbTE; [apply=>//|rewrite -leqNgt].
(*X*)  apply/allP=> /= _ /imageP [/= i _ ->].
(*X*)  rewrite rootE !hornerE horner_sum (bigD1 i) //=.
(*X*)  rewrite hornerM hornerC lagrangeE // eqxx mulr1 opprD addNKr.
(*X*)  rewrite big1 ?oppr0 // => j neq_ji.
(*X*)  by rewrite hornerM lagrangeE // (negPf neq_ji) mulr0.
(*X*)rewrite (leq_trans (size_add _ _)) // size_opp geq_max sp_le_n /=.
(*X*)rewrite (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP=> j _.
(*X*)rewrite (leq_trans (size_mul_leq _ _)) // size_polyC size_lagrange //.
(*X*)by move: (n) n_gt0 (_ == _) => [] // ? _ [].
(*A*)Qed.

End PolynomialsLagrange.

Section PolynomialsTaylor.
(**
Taylor formula for polynomials

*)
Import GRing.Theory.
Open Scope ring_scope.
Variable R: idomainType.

(*X*)(* This is the strongest statement I could prove *)
(*X*)(* uses max_poly_roots and nderiv_taylor *)
(*X*)Lemma Taylor_formula_strong (p : {poly R}) (x : R) (rs : seq R) :
(*X*)  (size p <= size rs)%N -> uniq rs ->
(*X*)  p = \sum_ (i < size p) p^`N(i).[x] *: ('X - x%:P) ^+ i.
(*X*)Proof.
(*X*)move=> sprs /max_poly_roots prs; apply/eqP; rewrite -subr_eq0.
(*X*)apply: contraTT isT => /prs; rewrite [(_ < _)%N]negbTE; [apply|rewrite -leqNgt].
(*X*)  apply/allP=> y y_rs; rewrite rootE hornerD hornerN subr_eq0; apply/eqP.
(*X*)  rewrite -[y in X in p.[X]](addrNK x) [_ + x]addrC.
(*X*)  rewrite nderiv_taylor; last exact: mulrC.
(*X*)  by rewrite horner_sum; apply: eq_bigr=> i _; rewrite !(hornerE, horner_exp).
(*X*)rewrite (leq_trans (size_add _ _)) // geq_max sprs /= size_opp.
(*X*)rewrite (leq_trans (size_sum _ _ _)) //; apply/bigmax_leqP=> i _.
(*X*)rewrite (leq_trans (size_scale_leq _ _)) //.
(*X*)by rewrite size_exp_XsubC (leq_trans _ sprs).
(*X*)Qed.

(*X*)Lemma natr_injP (D : idomainType) :
(*X*)  (forall n, (n%:R == 0 :> D) = (n == 0)%N) <-> injective (@GRing.natmul D 1).
(*X*)Proof.
(*X*)split=> [natr_eq0 i j|natr_inj n]; last by rewrite -(inj_eq natr_inj).
(*X*)wlog: i j / (j <= i)%N => [hwlog|].
(*X*)  by have [/hwlog//|/ltnW/hwlog/(_ (esym _))/esym] := leqP j i.
(*X*)by move=> /subnK<- /eqP; rewrite -subr_eq0 natrD addrK natr_eq0 => /eqP->.
(*X*)Qed.

(*X*) (* This is the statement we ask the students to prove *)
Hypothesis charR_eq0 : [char R] =i pred0.
Lemma Taylor_formula (p : {poly R}) (x : R) :
  p = \sum_ (i < size p) p^`N(i).[x] *: ('X - x%:P) ^+ i.
(*X*)Proof. (* Proof using the stronger version *)
(*X*)apply: (@Taylor_formula_strong _ _ [seq i%:R | i <- iota 0 (size p)]).
(*X*)  by rewrite size_map size_iota.
(*X*)by rewrite map_inj_uniq ?iota_uniq //; apply/natr_injP/charf0P.
(*X*)
(*X*)Restart. (* Proof for the students *)
(*X*)
Proof.
wlog: p x / x = 0 => [hwlog|->]; rewrite ?subr0; last first.
(*X*)  transitivity (\poly_(i < size p) p^`N(i).[0]);
(*X*)    last by rewrite poly_def.
(*X*)  apply/polyP=> /= i; rewrite coef_poly.
(*X*)  have [i_small|i_big]:= ltnP; last by rewrite nth_default.
  (*a*)by rewrite horner_coef0 coef_nderivn addn0 binn mulr1n.
rewrite -[LHS](comp_polyXaddC_K _ x) -[RHS](comp_polyXaddC_K _ x).
congr (_ \Po _); rewrite [LHS](hwlog _ 0 erefl) ?subr0 [RHS]raddf_sum /=.
rewrite size_comp_poly2; last first.
  by rewrite -[x%:P as X in 'X + X]opprK -[- x%:P]raddfN /= size_XsubC.
(*X*)apply: eq_bigr => i _.
(*X*)have nderivn_compXD q (a : R) j :
(*X*)  (q \Po ('X + a%:P))^`N(j) = q^`N(j) \Po ('X + a%:P).
       have /charf0P/natr_injP natr_inj := charR_eq0.
(*X*)  apply: (@mulfI _ j`!%:R%:P).
(*X*)     rewrite polyC_eq0; have/charf0P -> := charR_eq0.
     (*a*)by rewrite -lt0n fact_gt0.
(*X*)  rewrite !mul_polyC !scaler_nat -rmorphMn /= -!nderivn_def.
  (*a*)by elim: j => //= j ->; rewrite deriv_comp !derivE addr0 mulr1.
(*X*)rewrite nderivn_compXD horner_comp !hornerE // linearZ rmorphX /=.
(*X*)rewrite -['X - x%:P]comp_polyX -[x%:P as X in 'X + X]opprK.
(*X*)by rewrite -[- x%:P]raddfN /= comp_polyXaddC_K.
(*A*)Qed.

End PolynomialsTaylor.

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
  - we have rank v + rank u = n and we have Im v ⊂ Ker u
  - Hence we have Im v = Ker u
  - We deduce that Ker u ⊕ Im u = Im v ⊕ Im u = E

*)
Variables (F : fieldType) (n' : nat).
Let n := n'.+1.

Lemma ex_6_13 (u : 'M[F]_n):
  reflect (exists2 v : 'M_n, v * u = 0 & v + u \is a GRing.unit)
          ((kermx u + u == 1)%MS && mxdirect (kermx u + u)).
Proof.
(* Hint: use mxrank* lemmas and search on addsmx, submx and eqmx
sometimes. Don't forget about mxdirect_addsP and sub_kermxP. *)
apply: (iffP idP) => [|[v vMu vDu]]; last first.
  have rkvDu: \rank (v + u)%R = n by (*a*)rewrite mxrank_unit.
  have /eqP rkvDrku : (\rank v + \rank u)%N == n.
    by rewrite eqn_leq; (*a*)rewrite mulmx0_rank_max //= -{1}rkvDu mxrank_add.
  have sub_v_ku : (v <= kermx u)%MS by (*a*)apply/sub_kermxP.
  have /eqmxP/eqmx_sym eq_vu: (v == kermx u)%MS.
    rewrite -(geq_leqif (mxrank_leqif_eq _)) //.
(*X*)    rewrite -(leq_add2r (\rank u)) rkvDrku.
    (*a*)by rewrite mxrank_ker subnK // rank_leq_row.
  rewrite submx1 sub1mx -col_leq_rank mxdirectEgeq /=.
  (* use adds_eqmx to lift eq_vu to a sum *)
(*X*)  rewrite eq_vu (adds_eqmx eq_vu (eqmx_refl _)).
  (* Warning: - (u + v)%R  is a sum of matrices
              - (u + v)%MS is a sum of spaces
     use addmx_sub_adds and mxrankS
     to compare the rank (u + v) with dim (Im u + Im v) *)
(*X*)  have /mxrankS leq_rk := addmx_sub_adds (submx_refl v) (submx_refl u).
  (* finish using hypothesis *)
  (*a*)by rewrite !(leq_trans _ leq_rk) //= ?rkvDu ?rkvDrku.
move=> /andP [/eqmxP kuDu_eq1 /mxdirect_addsP kvDu_direct].
pose v := proj_mx (kermx u) u; exists v.
  (*a*)by apply/sub_kermxP; rewrite -[X in (X <= _)%MS]mul1r proj_mx_sub.
rewrite -row_free_unit -kermx_eq0.
apply/negP => /negP /rowV0Pn [x /sub_kermxP]; rewrite mulmxDr.
move=> /(canRL (addrK _)); rewrite sub0r => eq_xv_Nxu.
apply/negP; rewrite negbK; apply/eqP.
have : (x *m v <= kermx u :&: u)%MS.
(* Hint: use sub_*, proj_mx*, eqmx_*, mxdirect_addsP, *)
  (*a*)by rewrite sub_capmx proj_mx_sub eq_xv_Nxu eqmx_opp submxMl.
(*X*)rewrite kvDu_direct ?submx0 // => /eqP xv_eq0.
(*X*)move/eqP : eq_xv_Nxu; rewrite xv_eq0 eq_sym oppr_eq0 => /eqP.
(*X*)by move=> /sub_kermxP x_in_keru; move: xv_eq0; rewrite proj_mx_id.
(*A*)Qed.

End LinearAlgebra.

(*X*)(*
(*X*)*** Local Variables: ***
(*X*)*** coq-prog-args: ("-emacs-U" "-R" "/Users/lrg/coq/math-comp/mathcomp" "mathcomp" "-I" "/Users/lrg/coq/math-comp/mathcomp" ) ***
(*X*)*** End: ***
(*X*)*)
