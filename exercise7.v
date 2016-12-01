From mathcomp Require Import all_ssreflect all_algebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Open Scope ring_scope.

Section CPGE.
(**

*)
Section ex_6_12.
(** -------------------------------------------- *)
(** #<div class='slide'>#

* Exercices de mathématiques oraux X-ens Algebre 1

Determine the endomorphisms u such that Ker u = Im u.

Let E be a vector space (any dimension, but in Coq we reason in finite
dimension).

*)
Variables (F : fieldType) (n' : nat).
Let n := n'.+1.

Section Q1.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

** Question 1.

Let u be an endomorphism of E, such that Ker u = Im u and S be a
complement of Im u ("supplémentaire" in french), so that E is the
direct sum of S and Im u.

*)
Variable (u : 'M[F]_n) (S : 'M[F]_n).
Hypothesis eq_keru_imu : (kermx u :=: u)%MS.
Hypothesis S_u_direct : (S :&: u)%MS = 0.
Hypothesis S_u_eq1 : (S + u :=: 1)%MS.

Implicit Types (x y z : 'rV[F]_n). 
(**

*** Question 1.a.

Show that for all x in E, there is a unique pair (y, z) in S² such
that x = y + u (z), and pose v and z so that y = v(x) and z = w(x).

*)
Definition w := locked (proj_mx S u).
Definition v := locked (proj_mx u S * pinvmx u * proj_mx S u).
(**

Note that we used locking in order to protect w and v from expanding
unexpectedly during proofs.

</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

**** Question 1.a.i.
Prove the following lemmas.

*)
Lemma wS x : (x *m w <= S)%MS.
Proof.
unlock w.
(*D*)by rewrite proj_mx_sub.
(*A*)Qed.

Lemma vS x : (x *m v <= S)%MS.
Proof.
unlock v.
(*D*)by rewrite mulmxA proj_mx_sub.
(*A*)Qed.

Lemma w_id x : (x <= S)%MS -> x *m w = x.
Proof.
unlock w => xS.
(*D*)by rewrite proj_mx_id ?S_u_direct.
(*A*)Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#


**** Question 1.a.ii.

Reuse and adapt and the proof in the course.

- (hint: use mulmxKpV)

*)
Lemma Su_rect x : x = x *m w + (x *m v) *m u.
Proof.
unlock v w.
(*
remember we had t, z' and z
y := x *m proj_mx S u
t := x *m proj_mx u S
z' := t *m pinvmx u
z := z' *m proj_mx S u.
and x = y + z *m u
    z' *m u = z *m u
    z' *m u = t
*)
(*D*)rewrite -{1}(@add_proj_mx _ _ _ S u x) ?S_u_direct ?S_u_eq1 ?submx1 //.
(*D*)congr (_ + _); apply/eqP.
(*D*)rewrite -[x *m proj_mx u S](@mulmxKpV _ _ _ _ _ u) ?proj_mx_sub //.
(*D*)rewrite 2![x *m _ in X in _ == X]mulmxA -subr_eq0 -mulmxBl.
(*D*)apply/eqP/sub_kermxP.
(*D*)by rewrite eq_keru_imu proj_mx_compl_sub ?S_u_eq1 ?submx1.
(*A*)Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

**** Question 1.a.iii.
From the proof 

*)
Lemma Su_dec_eq0 y z : (y <= S)%MS -> (z <= S)%MS -> 
  (y + z *m u == 0) = (y == 0) && (z == 0).
Proof.
move=> yS zS; apply/idP/idP; last first.
  by move=> /andP[/eqP -> /eqP ->]; rewrite add0r mul0mx.
rewrite addr_eq0 -mulNmx => /eqP eq_y_Nzu.
have : (y <= S :&: u)%MS by rewrite sub_capmx yS eq_y_Nzu submxMl.
rewrite S_u_direct // submx0 => /eqP y_eq0.
move/eqP: eq_y_Nzu; rewrite y_eq0 eq_sym mulNmx oppr_eq0 eqxx /= => /eqP.
move=> /sub_kermxP; rewrite eq_keru_imu => z_keru.
have : (z <= S :&: u)%MS by rewrite sub_capmx zS.
by rewrite S_u_direct // submx0.
Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

deduce 

*)
Lemma Su_dec_uniq y y' z z' : (y <= S)%MS -> (z <= S)%MS -> 
                              (y' <= S)%MS -> (z' <= S)%MS -> 
  (y + z *m u == y' + z' *m u) = (y == y') && (z == z').
Proof.
(*D*)move=> yS zS y'S z'S; rewrite -subr_eq0 opprD addrACA -mulmxBl.
(*D*)by rewrite Su_dec_eq0 ?addmx_sub ?eqmx_opp // !subr_eq0.
(*A*)Qed.
(**
**** Question 1.a.iii.

Show some simplification lemmas
- the two first are direct
- the two last use Su_dec_uniq.

*)
Lemma u2_eq0 : u *m u = 0.
(*A*)Proof. by apply/sub_kermxP; rewrite eq_keru_imu. Qed.

Lemma u2K m (a : 'M_(m,n)) : a *m u *m u = 0.
(*D*)Proof. by rewrite -mulmxA u2_eq0 mulmx0. Qed.

Lemma v_id x : (x <= S)%MS -> (x *m u) *m v = x.
Proof.
(*D*)move=> xS; have /eqP := Su_rect (x *m u).
(*D*)rewrite -[X in X == _]add0r Su_dec_uniq ?sub0mx ?vS ?wS //.
(*D*)by move=> /andP [_ /eqP <-].
(*A*)Qed.

Lemma w0 x : (x <= S)%MS -> (x *m u) *m w = 0.
Proof.
(*D*)move=> xS; have /eqP := Su_rect (x *m u).
(*D*)rewrite -[X in X == _]add0r Su_dec_uniq ?sub0mx ?vS ?wS //.
(*D*)by move=> /andP [/eqP <-].
(*A*)Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

*** Question 1.b.

- Show that v is linear.
- Show that u o v + v o u = 1.

*)
Lemma add_uv_vu : v *m u + u *m v = 1.
Proof.
(*D*)apply/row_matrixP => i; rewrite !rowE; move: (delta_mx _ _) => x.
(*D*)rewrite mulmx1 mulmxDr !mulmxA {2}[x]Su_rect mulmxDl u2K addr0.
(*D*)by rewrite v_id ?wS // addrC -Su_rect.
(*A*)Qed.
(** #</div># *)
(** -------------------------------------------- *)
(** #<div class='slide'>#

*** Question 1.c.

- Show that w is linear.
- Show that u o w + w o u = u.

*)
Lemma add_wu_uw : w *m u + u *m w = u.
Proof.
(*D*)apply/row_matrixP => i; rewrite !rowE; move: (delta_mx _ _) => x.
(*D*)rewrite mulmxDr !mulmxA {2}[x]Su_rect mulmxDl u2K addr0 w0 ?wS // addr0.
(*D*)by have /(canLR (addrK _)) <- := Su_rect x; rewrite mulmxBl u2K subr0.
(*A*)Qed.

End Q1.

End ex_6_12.
End CPGE.
