From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Scope ring_scope.

(**

Endomorphisms such that Ker u + Im u = E.

*)
Section CPGE.

Lemma ex_6_13 (F : fieldType) (n : nat) (u : 'M[F]_n.+1):
  reflect (exists2 v, v * u = 0
                    & v + u \is a GRing.unit)
          ((mxdirect (kermx u + u)%MS) && (kermx u + u == 1)%MS).
Proof.
(*D*)apply: (iffP idP) => [|[v vMu vDu]]; last first.
(*D*)  have rkvDu: \rank (v + u)%R = n.+1 by rewrite mxrank_unit.
(*D*)  have /eqP rkvDrku : (\rank v + \rank u)%N == n.+1.
(*D*)    by rewrite eqn_leq mulmx0_rank_max //= -{1}rkvDu mxrank_add //.
(*D*)  have /eqmxP/eqmx_sym eq_vu: (v == kermx u)%MS.
(*D*)    rewrite -(geq_leqif (mxrank_leqif_eq _)); last by apply/sub_kermxP.
(*D*)    rewrite -(leq_add2r (\rank u)) rkvDrku.
(*D*)    by rewrite mxrank_ker subnK // rank_leq_row.
(*D*)  rewrite submx1 sub1mx  -col_leq_rank mxdirectEgeq /=.
(*D*)  rewrite eq_vu (adds_eqmx eq_vu (eqmx_refl _)).
(*D*)  have /mxrankS leq_rk := addmx_sub_adds (submx_refl v) (submx_refl u).
(*D*)  by rewrite !(leq_trans _ leq_rk) //= ?rkvDu ?rkvDrku.
(*D*)move=> /andP [kuDu_direct /eqmxP kuDu_eq1].
(*D*)pose v := (proj_mx (kermx u) u); exists v.
(*D*)  by apply/sub_kermxP; rewrite -[X in (X <= _)%MS]mul1r proj_mx_sub.
(*D*)rewrite -row_free_unit -kermx_eq0.
(*D*)apply/negP => /negP /rowV0Pn [x /sub_kermxP]; rewrite mulmxDr.
(*D*)move=> /(canRL (addrK _)); rewrite sub0r => eq_xv_Nxu.
(*D*)apply/negP; rewrite negbK; apply/eqP.
(*D*)have : (x *m v <= kermx u :&: u)%MS.
(*D*)  by rewrite sub_capmx proj_mx_sub eq_xv_Nxu eqmx_opp submxMl.
(*D*)rewrite (mxdirect_addsP _) ?submx0 // => /eqP xv_eq0.
(*D*)move/eqP : eq_xv_Nxu; rewrite xv_eq0 eq_sym oppr_eq0 => /eqP.
(*D*)move=> /sub_kermxP x_in_keru; move: xv_eq0; rewrite proj_mx_id //.
(*D*)by rewrite (mxdirect_addsP _).
(*A*)Qed.

End CPGE.
