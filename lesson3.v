From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 

----
** Roadmap for lessons 3 and 4

  - finite types
  - big operators
  - playing with graph

*)

(**
----
** Lesson 3 

- The SSR gives some support for finite types.
- 'I_n is the the set of natural numbers smaller than n.
- a : 'I_n is composed of a value m and a proof that m <= n.

- Example : oid modifies the proof part with an equivalent one.
*)

Definition oid n (x : 'I_n) : 'I_n.
pose v := nat_of_ord x.
pose H := ltn_ord x.
pose H1 := leq_trans H (leqnn n).
exact: Ordinal H1.
Defined.

(** 

 ** Note 
   - nat_of_ord is a coercion (see H)
   - 'I_0 is an empty type
*)

Lemma empty_i0 (x : 'I_0) : false.
Proof. 
case x. 
by [].
Qed.

(** 
  ** Equality

  - Every finite type is also an equality type.
  - For 'I_n, only the value matters

*)

Definition i3 := Ordinal (isT : 3 < 4).

Lemma ieq : oid i3 == i3.
Proof.
exact: eqxx.
Qed.

(** 
  ** Sequence 
 - a finite type can be seen as a sequence
 - enum T gives this sequence.
 - it is duplicate free.
 - it relates to the cardinal of a finite type
*)

Lemma iseq n (x : 'I_n) : x \in 'I_n.
Proof.
have mem_enum := mem_enum.
have enum_uniq := enum_unique.
have cardT := cardT.
have cardE := cardE.
by [].
Qed.

(** 
  ** Booleans 
 - for finite type, boolean reflection can be extended to quantifiers
*)

Lemma iforall (n : nat) : [forall x: 'I_n, x < n].
Proof. 
apply/forallP.
rewrite /=.
move=> x.
exact: ltn_ord.
Qed.

Lemma iexists  (n : nat) : (n == 0) || [exists x: 'I_n, x == 0 :> nat].
Proof.
case: n.
by [].
move=> n.
apply/existsP.
pose H : 0 < n.+1 := isT.
pose x := Ordinal H.
exists x.
by [].
Qed.

(** 
  ** Selecting an element
 - pick selects an element that has a given property 
 - pickP triggers the reflection
*)

Check pick.

Definition izero n (x : 'I_n) := odflt x [pick i : 'I_n | i == 0 :> nat].

Lemma izero_def n (x : 'I_n.+1) : izero x == 0 :> nat.
Proof.
rewrite /izero.
case: pickP.
rewrite /=.
by [].
rewrite /=.
move=> H.
have := H (Ordinal (isT : 0 < n.+1)).
rewrite /=.
by [].
Qed.

(**
  ** Building finite types
  - SSR automatically discovers the pair of two finite types is finite
  - For functions there is an explicit construction [ffun x => body] 
*)

Lemma ipair : [forall x : 'I_3 * 'I_4, x.1 * x.2 < 12].
Proof.
apply/forallP.
rewrite /=.
case.
rewrite /=.
move=> a b.
have H := ltn_mul.
rewrite -[12]/(3 * 4).
by apply: H.
Qed.

Lemma ifun : [exists f : {ffun 'I_3 -> 'I_4}, forall x, f x == x :> nat].
Proof.
apply/existsP.
rewrite /=.
have H : forall n x, x < n -> x < n.+1.
move=> n x H.
rewrite ltnS.
by rewrite ltnW.
exists [ffun x : 'I_3 => Ordinal (H 3 x (ltn_ord x))].
apply/forallP.
move=> x.
have H1 := ffunE.
rewrite H1.
rewrite /=.
by [].
Qed.

(**
   ----
   ----
 **)


(**
  ** Big operators
   --  provide a library to manipulate iterations in SSR
   -- this is an encapsulation of the fold function
 **)

Section F.

Definition f (x : nat) := 2 * x.
Definition g x y := x + y.
Definition r := [::1; 2; 3].

Lemma bfold : foldr (fun val res => g (f val) res) 0 r = 12.
Proof.
rewrite /=.
rewrite /f.
rewrite /g.
by [].
Qed.

End F.

(** 
   ** Notation

   - iteration is provided by the \big notation
   - the basic operation is on list
   - special notations are introduced for usual case (\sum, \prod, \bigcap ..) 
*)

Lemma bfoldl : \big[addn/0]_(i <- [::1; 2; 3]) i.*2 = 12.
Proof.
rewrite big_cons.
rewrite big_cons.
rewrite big_cons.
rewrite big_nil.
by [].
Qed.

Lemma bfoldlm : \big[muln/1]_(i <- [::1; 2; 3]) i.*2 = 48.
Proof.
rewrite big_cons.
rewrite big_cons.
rewrite big_cons.
rewrite big_nil.
by [].
Qed.

(** 
   ** Range 
   - different ranges are provided
*)

Lemma bfoldl1 : \sum_(1 <= i < 4) i.*2 = 12.
Proof.
have H := big_ltn.
have H1 := big_geq.
rewrite big_ltn.
  rewrite big_ltn.
    rewrite big_ltn.
      rewrite big_geq.
        by [].
      by [].
    by [].
  by [].
by [].
Qed.

Lemma bfoldl2 : \sum_(i < 4) i.*2 = 12.
Proof.
rewrite big_ord_recl.
rewrite /=.
rewrite big_ord_recl.
rewrite /=.
rewrite big_ord_recl.
rewrite big_ord_recl.
rewrite big_ord0.
by [].
Qed.

Lemma bfoldl3 : \sum_(i : 'I_4) i.*2 = 12.
Proof.
exact: bfoldl2.
Qed.

(** 
   ** Filtering 
   - it is possible to filter elements from the range 
*)

Lemma bfoldl4 : \sum_(i <- [::1; 2; 3; 4; 5; 6] | ~~ odd i) i = 12.
Proof.
have big_pred0 := big_pred0.
have big_hasC := big_hasC.
pose x :=  \sum_(i < 8 | ~~ odd i) i.
pose y :=  \sum_(0 <= i < 8 | ~~ odd i) i.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_cons.
rewrite /=.
rewrite big_nil.
by [].
Qed.

(** 
   ** Switching range
   - it is possible to change representation (big_nth, big_mkord).
*)

Lemma bswitch :  \sum_(i <- [::1; 2; 3]) i.*2 = \sum_(i < 3) (nth 0 [::1; 2; 3] i).*2.
Proof.
have H := big_nth.
rewrite (big_nth 0).
rewrite /=.
have H1 := big_mkord.
rewrite big_mkord.
by [].
Qed.

(**
  ** Big operators and equality
  - one can exchange function and/or predicate 
 *)

Lemma beql : 
  \sum_(i < 4 | odd i || ~~ odd i) i.*2 =  \sum_(i < 4) i.*2.
Proof.
have H := eq_bigl.
apply: eq_bigl.
move=> u.
by case: odd.
Qed.

Lemma beqr : 
  \sum_(i < 4) i.*2 = \sum_(i < 4) (i + i).
Proof.
have H := eq_bigr.
apply: eq_bigr.
rewrite /=.
move=> u _.
rewrite addnn.
by [].
Qed.

Lemma beq : 
  \sum_(i < 4 | odd i || ~~ odd i) i.*2 = \sum_(i < 4) (i + i).
Proof.
have H := eq_big.
apply: eq_big => [u|i Hi]; first by case: odd.
by rewrite addnn.
Qed.

(**
  ** Monoid structure
  - one can use associativity to reorder the bigop
 *)

Lemma bmon1 : \sum_(i <- [::1; 2; 3]) i.*2 = 12.
Proof.
have H := big_cat.
rewrite -[[::1; 2; 3]]/([::1] ++ [::2; 3]).
rewrite big_cat.
rewrite /=.
rewrite !big_cons !big_nil.
by [].
Qed.

Lemma bmon2 : \sum_(1 <= i < 4) i.*2 = 12.
Proof.
have H := big_cat_nat.
rewrite (big_cat_nat _ _ _ (isT: 1 <= 2)).
  rewrite /=.
  rewrite big_ltn //=.
  rewrite big_geq //.
  by rewrite 2?big_ltn //= big_geq.
by [].
Qed.

Lemma bmon3 : \sum_(i < 4) i.*2 = 12.
Proof.
have H := big_ord_recl.
have H1 := big_ord_recr.
rewrite big_ord_recr.
rewrite /=.
rewrite !big_ord_recr //=.
rewrite big_ord0.
by [].
Qed.

Lemma bmon4 : \sum_(i < 8 | ~~ odd i) i = 12.
Proof.
have H := big_mkcond.
rewrite big_mkcond.
rewrite /=.
rewrite !big_ord_recr /=.
rewrite big_ord0.
by [].
Qed.

(**
  ** Abelian Monoid structure
  - one can use communitativity to massage the bigop
 *)


Lemma bab : \sum_(i < 4) i.*2 = 12.
Proof.
have H := bigD1.
pose x := Ordinal (isT: 2 < 4).
rewrite (bigD1 x).
  rewrite /=.
  rewrite big_mkcond /=.
  rewrite !big_ord_recr /= big_ord0.
  by [].
by [].
Qed.

Lemma bab1 : \sum_(i < 4) (i + i.*2) = 18.
Proof.
have H := big_split.
rewrite big_split /=.
rewrite !big_ord_recr ?big_ord0 /=.
by [].
Qed.

Lemma bab2 : \sum_(i < 3) \sum_(j < 4) (i + j) = \sum_(i < 4) \sum_(j < 3) (i + j).
Proof.
have H := exchange_big.
have H1 := reindex_inj.
rewrite exchange_big.
rewrite /=.
apply: eq_bigr.
move=> i _.
apply: eq_bigr.
move=> j _.
by rewrite addnC.
Qed.

(**
  ** Distributivity
  - one can use exchange sum and product 
 *)

Lemma bab3 : \sum_(i < 4) (2 * i) = 2 * \sum_(i < 4) i.
Proof.
have H := big_distrr.
by rewrite big_distrr.
Qed.

Lemma bab4 : 
  (\prod_(i < 3) \sum_(j < 4) (i ^ j)) = 
  \sum_(f : {ffun 'I_3 -> 'I_4}) \prod_(i < 3) (i ^ (f i)).
Proof.
have H := big_distr_big.
have H1 := big_distr_big_dep.
rewrite  (big_distr_big ord0).
rewrite /=.
apply: eq_bigl.
move=> f.
rewrite /=.
apply/forallP.
rewrite /=.
by [].
Qed.


(**
  ** Property, Relation and Morphism 
 *)

Lemma bap n : ~~ odd (\sum_(i < n) i.*2). 
Proof.
have H := big_ind.
have H1 := big_ind2.
have H2 := big_morph.
elim/big_ind: _.
- by [].
- move=> x y.
  rewrite odd_add.
  case: odd.
     by [].
  by [].
move=> i _.
by rewrite odd_double.
Qed.



