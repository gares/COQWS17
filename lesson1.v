(** 

To play this document inside your browser use ALT-N and ALT-P.

----
#<div class="slide vfill">#
** Objective of this course

  Give you access to the #<a href="http://math-comp.github.io/math-comp/">Mathematical Components library</a>#

  - formalization principles
  - proof language
  - familiarize with some theories


#</div>#

----------------------------------------------------------
#<div class="slide vfill">#
** Why another library? Why another language?

  - large, consistent, library organized as a programming language
    library (interfaces, overload, naming conventions, ...)
  - maintainable in the long term (compact, stable, ...)
  - validated on large formalization projects

#</div>#

----------------------------------------------------------
#<div class="slide vfill">#
** Roadmap of the first 2 lessons

  - the small scale reflection approach (ssr)
  - the ssreflect tactic language (ssr)
  - basic libraries (ssrbool, ssrnat, seq)

#</div>#

----------------------------------------------------------
#<div class="slide vfill">#
** Disclaimer: this is not standard Coq

  - things are done differently, very differently, than usual
  - it is not easy to appreciate the benefits on small examples,
    but we will try hard ;-)
  - not enough time to explain eveything, I'll focus on
    intuition rather than technical details
#</div>#

----------------------------------------------------------
----------------------------------------------------------
#<div class="slide">#
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
#</div>#
----------------------------------------------------------
#<div class="slide">#
** A taste of boolean reflection by examples
  - these examples are artificial
  - in the library things are done in a slightly different way
#</div>#
------------------------------------------------------
#<div class="slide">#
*** The first predicate
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

(** 
#</div>#
------------------------------------------------------
#<div class="slide">#
 *** The first proof about leq
   - [... = true] to "state" something
   - proof by computation
   - [by []] to say, provable by trivial means (no mean is inside []).
   - [by tac] to say: tac must solve the goal (up to trivial leftovers)
*)
Lemma leq0n n : (0 <= n) = true.
Proof. (* compute. *) by []. Qed.

(**  
#</div>#
------------------------------------------------------
#<div class="slide">#
*** Another lemma about leq
   - equality as a double implication
   - naming convention
*)
Lemma leqSS n m : (n.+1 <= m.+1) = (n <= m).
Proof. (* simpl. *) by []. Qed.

(** 
#</div>#
------------------------------------------------------
#<div class="slide">#
*** Lets (not) use these lemmas
   - elim with naming and automatic clear of n
   - indentation for subgoals
   - no need to mention lemmas proved by computation
   - apply, exact, rewrite
*)
Lemma leqnn n : (n <= n) = true.
Proof.
(*#
elim: n => [|m IHm].
  by apply: leq0n.  exact: leq0n.
by rewrite leqSS IHm.
#*)
by elim: n. Qed.

(** 
#</div>#
------------------------------------------------------
#<div class="slide">#
*** Connectives can be booleans too *)
Definition andb (b1 b2 : bool) : bool :=
  if b1 then b2 else false.
Infix "&&" := andb.

Definition orb (b1 b2 : bool) : bool :=
  if b1 then true else b2.
Infix "||" := orb.

Definition negb b : bool :=
  if b then false else true.
Notation "~~ b" := (negb b).

(** 
#</div>#
------------------------------------------------------
#<div class="slide">#
*** Proofs by truth tables
   - we can use EM to reason about boolean predicates
     and connectives
   - case
   - bookkeeping [/=]
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

(** 
#</div>#
------------------------------------------------------
#<div class="slide">#
*** Bookkeeping 101
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
#</div>#
------------------------------------------------------
#<div class="slide vfill">#
** Recap (ssr approach and basic tactics)
   - boolean predicates and connectives
   - think "up to" computation
   - case, elim, move, :, =>, basic rewrite
   - if-is-then-else, .+1
   - naming convetion

#</div>#
------------------------------------------------------
------------------------------------------------------
#<div class="slide">#
** The real MathComp library
  
   Things to know:
   - [Search head_symbol (pat _ term) "string" name]
   - [(a < b)] is a notation for [(a.+1 <= b)]
   - [==] stands for computable equality (overloaded)
   - [!=] is [~~ (_ == _)]
   - [is_true] coercion
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
#</div>#
-------------------------------------------------------------
#<div class="slide">#
** Equality
   - privileged role (many lemmas are stated with = or is_true)
   - the [eqP] view: "is_true (a == b)   <->    a = b"
   - [=> /eqP] (both directions)
   - [=> ->] (on the fly rewrite, "subst")
   - notation [.*2]

*)
Lemma test_eqP n m : n == m -> n.+1 + m.+1 = m.+1.*2.
Proof.
(*#
Check eqP.
move=> /eqP. move=> /eqP. move=> /eqP Enm. rewrite Enm.
Search _ (_ + _) _.*2 in ssrnat.
exact: addnn.
#*)
by move=> /eqP ->; rewrite -addnn. Qed.

(**
#</div>#
-------------------------------------------------------------
#<div class="slide">#
 ** Infix [==] is overloaded
   - and [eqP] is too
*)
Lemma test2_eqP b1 b2 : b1 == ~~ b2 -> b1 || b2.
Proof.
(*
Search _ orb in ssrbool.
*)
by move=> /eqP->; exact: orNb.
Qed.

(**
#</div>#
------------------------------------------------------------
#<div class="slide">#
** Views are just lemmas 
   (plus some automatic adaptors)
   - lemmas like [A -> B] can be used as views too
   - boolean aconnectives have associated views
   - [=> [ ... ]]

*)

Lemma test_leqW i j k : (i <= k) && (k.+1 <= j) -> i <= j.+1.
Proof.
(*# move=> /andP. case. move=> /leqW. move=> leq_ik1. #*)
move=> /andP[/leqW leq_ik1 /leqW leq_k1j1].
exact: leq_trans leq_ik1 leq_k1j1.
Qed.

(**
#</div>#
------------------------------------------------------------
#<div class="slide">#
** The reflect predicate
   - [reflect P b] is the preferred way to state that
     the predicate [P] (in [Prop]) is logically equivalent
     to [b=true]

*)
Module reflect_for_eqP.

Print reflect.

Fixpoint eqn m n :=
  match m, n with
  | 0, 0 => true
  | j.+1,k.+1 => eqn j k
  | _, _ => false
  end.
Arguments eqn !m !n.

(**
#</div>#
----------------------------------------------------------
#<div class="slide">#
*** Proving the reflection lemma for eqn
    - the convenience lemma [iffP]
    - the [congr] tactic
    - trivial branches //
    - loaded induction [elim: n m]

*)
Lemma myeqP m n : reflect (m = n) (eqn m n).
Proof.
(*#
apply: (iffP idP) => [|->]; last by elim: n.
elim: m n; first by case.
move=> n IHn m eq_n1m.
case: m eq_n1m => // m eq_n1m1.
congr (_.+1).
exact: IHn.
#*)
apply: (iffP idP) => [|->]; last by elim: n.
by elim: m n => [|m IHm] // [|n] // /IHm->.
Qed.

Lemma test_myeqP n m : (eqn n m) -> m = n.
Proof. by move=> /myeqP ->. Qed.

End reflect_for_eqP.

(** 
#</div># 
--------------------------------------
#<div class="slide">#
** rewrite, one command to rule them all
  - rewrite
  - side condition and // ? 
  - rewrite a boolean predicate (is_true hides an eqaution)

*)

Lemma test_leq_cond p : prime p -> p.-1.+1 + p = p.*2.
Proof.
(*#
move=> pr_p.
Search _ predn in ssrnat.
rewrite prednK.
  by rewrite addnn.
Search _ prime leq 0.
by apply: prime_gt0.
#*)
by move=> pr_p; rewrite prednK ?addnn // prime_gt0.
Qed.

(**
#</div># 
----
#<div class="slide">#
** References for this lesson
  - SSReflect #<a href="https://hal.inria.fr/inria-00258384">manual</a>#
  - documentation of the
       #<a href="http://math-comp.github.io/math-comp/htmldoc/libgraph.html">library</a>#
    - in particular #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.ssrbool.html">ssrbool</a>#
    - in particular #<a href="http://math-comp.github.io/math-comp/htmldoc/mathcomp.ssreflect.ssrnat.html">ssrnat</a>#
  - #<a href="http://math-comp.github.io/mcb/">Book</a># (draft) on the Mathematical Components library
    #<img src="https://math-comp.github.io/mcb/cover-front-web.png"/>#
#</div># 
*)
