(** 

** Objective of this course

  Give you access to the Mathematical Components library

  - formalization principles
  - proof language
  - familiarize with some theories

  #<a href="http://math-comp.github.io/math-comp/">MathComp website</a>#

----
** Why another library? Why another language?
  - large, consistent, library organized as a programming language
    library (interfaces, overload, naming conventions, ...)
  - maintainable in the long term (compact, stable, ...)
  - validated on large formalization projects


----
** Roadmap of the first 2 lessons

  - the small scale reflection approach
  - the ssreflect tactic language
  - basic libraries (ssrbool, ssrnat, seq)


----
** Disclaimer: this is not standard Coq

  - things are done differently, very differently, than usual
  - it is not easy to appreciate the benefits on small examples,
    but we will try hard ;-)
  - not enough time to explain eveything, I'll focus on
    intuition rather than technical details


----
** The SSR approach

  - when a concept is "computable", lets represent it as a
    computable function, not as an inductive relation
  - Coq knows how to compute, even symbolically, and computation is
    a very stable form of automation
  - functions to bool are a "simple" concept in type theory
    - EM holds
    - UIP holds

*)

From mathcomp Require Import all_ssreflect.

Module BooleanReflection.
(**

----
** A taste of boolean reflection by examples
  - these examples are artificial
  - in the library things are done in a slightly different way

----
*** Example:
   - order ralation on nat is a program
   - if-is-then syntax (simply a 2-way match-with-end)
   - [.+1] syntax (postfix notations [.something] are recurrent)

*)
Fixpoint leq (n m : nat) : bool :=
  if n is p.+1 then
    if m is q.+1 then leq p q
    else false
  else true.

Arguments leq !n !m.
Infix "<=" := leq.

(** *** Example:
   - [... = true] to "state" something
   - proof by computation
   - [by []] to say, provable by trivial means (no mean is inside []).
   - [by tac] to say "tac should solve the goal (up to trivial leftovers)"
*)
Lemma leq0n n : (0 <= n) = true.
Proof. (* compute. *) by []. Qed.

(** *** Example:
   - equality as a double implication
   - naming convention
*)
Lemma leqSS n m : (n.+1 <= m.+1) = (n <= m).
Proof. (* simpl. *) by []. Qed.

(** *** Example:
   - elim with naming and automatic clear of n
   - indentation for subgoals
   - no need to mention lemmas proved by computation
   - apply, exact, rewrite
*)
Lemma leqnn n : (n <= n) = true.
Proof.
(*
elim: n => [|m IHm].
  by apply: leq0n.  (* exact: leq0m. *)
by rewrite leqSS IHm.
*)
by elim: n. Qed.

(** *** Example:
   - connectives can be booleans too
*)
Definition andb (b1 b2 : bool) : bool :=
  if b1 then b2 else false.
Infix "&&" := andb.

Definition orb (b1 b2 : bool) : bool :=
  if b1 then true else b2.
Infix "||" := orb.

Definition negb b : bool :=
  if b then false else true.
Notation "~~ b" := (negb b).

(** *** Example:
   - we can use EM to reason about boolean predicates
     and connectives
   - case
   - bookkeeping /=
   - naming convention: C suffix
*)
Lemma andbC b1 b2 : (b1 && b2) = (b2 && b1).
Proof.
(*
case: b1 => /=.
  by case: b2.
by case: b2.
*)
by case: b1; case: b2. Qed.

(** *** Example:
   - defective case (stack model, the _top_ implicit tactic argument)
   - tactic=>
   - tactic:        (caveat: tactic != apply or exact)
   - "rename", "reorder"
*)
Lemma negb_and : forall b c, ~~ (b && c) = ~~ b || ~~ c.
Proof.
(*
move=> b. move=> c. move: b. move: c.
move=> c b. move: b c.
move=> b; case: b; move=> c; case: c.
*)
by case; case. Qed.

End BooleanReflection.
(**

----
** Recap (ssr approach and basic tactics)
   - boolean predicates and connectives
   - think "up to" computation
   - case, elim, move, :, =>, basic rewrite
   - if-is-then-else, .+1
   - naming convetion


-----
** Now we use the real MathComp library
  
   Things to know:
   - [Search head_symbol (pat _ tern) "string" name]
   - [(a < b)] is a notation for [(a.+1 <= b)]
   - [==] stands for computable equality (overloaded)
   - [is_true] coercion
   - [!=] is [~~ (_ == _)]
*)
Search _ (_ <= _) in ssrnat.
Locate "_ < _".
Check (forall x, x.+1 <= x).
Search _ orb "C" in ssrbool.
Print commutative.
Check (3 == 4) || (3 <= 4).
Eval compute in (3 == 4) || (3 <= 4).
Check (true == false).
Check (3 != 4).

Lemma test_is_true_coercion : true.
Proof. unfold is_true. by []. Qed.


(**

---
** Equality:
   - privileged role (many lemmas are stated with = or is_true)
   - the eqP view: "is_true (a == b)   <->    a = b"
   - => /eqP (both directions)
   - => -> (on the fly rewrite, "subst")
   - notation .*2

*)
Lemma test_eqP n m : n == m -> n.+1 + m.+1 = m.+1.*2.
Proof.
(*
move=> /eqP. move=> /eqP. move=> /eqP Enm. rewrite Enm.
Search _ (_ + _) _.*2 in ssrnat.
exact: addnn.
*)
by move=> /eqP ->; rewrite -addnn. Qed.

(**

---
** (_ == _) is overloaded
   - and [eqP] is too
*)
Lemma test2_eqP b1 b2 : b1 == ~~ b2 -> b1 || b2.
Proof.
(*
Search _ orb in ssrbool.
by move: E => /eqP ->; rewrite orNb.
*)
by move=> /eqP->; exact: orNb.
Qed.

(**
---
** Views are just lemmas (plus some automatic adaptors)
   - lemmas like A->B can be used as views too
   - boolean aconnectives have associated views
   - => [ ... ]
*)

Lemma test_leqW i j k : (i <= k) && (k.+1 <= j) -> i <= j.+1.
Proof.
(* move=> /andP. case. move=> /leqW. move=> leq_ik1. *)
move=> /andP[/leqW leq_ik1 /leqW leq_k1j1].
exact: leq_trans leq_ik1 leq_k1j1.
Qed.

(**
---
** Trivial branches
   - => [ | ].
   - => //
*)
Lemma my_leqW m n : m <= n -> m <= n.+1.
Proof.
(*
elim: m n => [ // |n IHn [ // |m] /= leq_Snm].
exact: IHn.
*)
by elim: m n => // n IHn [|m] // /IHn.
Qed.

(** 
---
** rewrite, one command to rule them all
  - rewrite
  - side condition and // ? 
*)




(**
---
** The reflect predicate
   - [reflect P b] is the preferred way to state that
     the predicate [P] (in [Prop]) is logically equivalent
     to [b=true]
   - This is a fake example (no overloading)
*)
Module reflect_for_eqP.

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

(** *** Example:
    - elim: n m.
    - iffP
    - congr
*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
(*
apply: (iffP idP) => [|->]; last by elim: n.
elim: m n; first by case.
move=> n IHn m eq_n1m.
case: m eq_n1m => // m eq_n1m1.
congr (_.+1).
exact: IHn.
*)
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
Qed.

Print reflect.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.



(**
--- Connectives and views


*)

(*

Lemma leqW m n : m <= n = true -> m <= n.+1 = true.
Proof.
(* move=> leq_nm. move: leq_nm. move: m. move: n. *)
(* move=> n m leq_nm. move: n m leq_nm => n m leq_nm. *)
(*move: n m leq_nm; elim.*)
(*
elim: n m leq_nm => [ // |n IHn m leq_Snm].
case: m leq_Snm => [ // | m leq_SnSm /=].
by apply: IHn.
*)
(*
elim: n m leq_nm => [ // |n IHn [ // |m] /= leq_Snm].
exact: IHn.
*)
by elim: m n => // n IHn [|m] // /IHn.
*)

(** --------------------------------------------------------- *)

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise:
    - look for lemmas supporting contrapositive reasoning
*)
Lemma bool_gimmics1 p a : a != 3 -> a.+1 != 4.
Proof. by apply: contra. Qed.

Lemma bool_gimmics2 p q r : ~~ p && (r == q) -> q ==> (p || r).
Proof. by move=> /andP[/negbTE-> /eqP->]; exact: implybb. Qed.

(** *** Exercise:
   - it helps to find out what is behind ./2 and ./* in order to Search
   - any proof would do, but there is one not using implyP
*)
Lemma view_gimmics1 p a b : p -> (p ==> (a == b.*2)) -> a./2 = b.
(*D*)Proof. by move=> -> /eqP->; exact: doubleK. Qed.

(** *** Exercise: proove that! *)
Lemma Pirce p q : ((p ==> q) ==> p) ==> p.
(*D*)Proof. by case: p; case: q. Qed.


(** *** Exercise:
   - The only tactics allowed are rewrite and by
   - Use Search to find the relevant lemmas (all are good but for
     ltn_neqAle) or browse the #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.ssrnat.html">online doc</a>#
   - Proof sketch
        m < n = ~~ (n <= m)
              = ~~ (n == m || n < m)
              = n != m && ~~ (n < m)
              = ...
*)
Lemma ltn_neqAle m n : (m < n) = (m != n) && (m <= n).
(*D*)Proof. by rewrite ltnNge leq_eqVlt negb_or -leqNgt eq_sym. Qed.


(** *** Exercise:
  - There is no need to prove reflect with iffP: here just use rewrite and exact
  - Check out the definitions and theory of leq and maxn
  - Proof sketch:
   n <= m = n - m == 0
          = m + n - m == m + 0
          = maxn m n == m
*)
Lemma maxn_idPl m n : reflect (maxn m n = m) (m >= n).
(*D*)Proof. by rewrite -subn_eq0 -(eqn_add2l m) addn0 -maxnE; exact: eqP. Qed.



(** --------------------------------------------------------- *)

(** ** Recap:
   - => intro pattern (names, views, //, /=, {}, [])
   - rewrite lem -lem // /= /def
   - naming convention: addnC, eqP, orbN, orNb, ...
   - notations: .+1, if-is-then-else

*)

(** ** Spec lemmas
   - Inductive predicates to drive the proof
*)
CoInductive leq_xor_gtn m n : bool -> bool -> Set :=
  | LeqNotGtn of m <= n : leq_xor_gtn m n true false
  | GtnNotLeq of n < m  : leq_xor_gtn m n false true.

Lemma leqP m n : leq_xor_gtn m n (m <= n) (n < m).
Proof.
by rewrite ltnNge; case le_mn: (m <= n); constructor; rewrite // ltnNge le_mn.
Qed.

(*
Lemma test_leqP m n1 n2 : (m <= minn n1 n2) = (m <= n1) && (m <= n2).
Proof.
rewrite /minn ltnNge. case: (leqP n2 n1); case: (leqP m).
give_up.
wlog le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => ?; last rewrite minnC andbC; auto.
by rewrite /minn ltnNge le_n21 /= andbC; case: leqP => // /leq_trans->.
Qed.
*)

CoInductive compare_nat m n : bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : compare_nat m n true false false
  | CompareNatGt of m > n : compare_nat m n false true false
  | CompareNatEq of m = n : compare_nat m n false false true.

Lemma ltngtP m n : compare_nat m n (m < n) (n < m) (m == n).
Proof.
rewrite ltn_neqAle eqn_leq; case: ltnP; first by constructor.
by rewrite leq_eqVlt orbC; case: leqP; constructor; first apply/eqnP.
Qed.



(** ** Sequences
  - an alias for lists (used to be differnt)
  - many notations
*)
Check [:: 3 ; 4].
Check [::] ++ [:: true ; false].
Eval compute in [seq x.+1 | x <- [:: 1; 2; 3]].
Eval compute in rcons [:: 4; 5] 3.
Eval compute in [seq x <- [::3; 4; 5] | odd x ].
Eval compute in 3 \in [:: 7; 4; 3].
Eval compute in all odd [:: 3; 5]. 




(* have, seq, elim/foo, case: leqP *)

