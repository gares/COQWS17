From mathcomp Require Import all_ssreflect.

Implicit Type p q r : bool.
Implicit Type m n a b c : nat.

(** *** Exercise:
    - look for lemmas supporting contrapositive reasoning
*)
Lemma bool_gimmics1 p a : a != 3 -> a.+1 != 4.
(*D*)Proof. by apply: contra. Qed.

Lemma bool_gimmics2 p q r : ~~ p && (r == q) -> q ==> (p || r).
(*D*)Proof. by move=> /andP[/negbTE-> /eqP->]; exact: implybb. Qed.

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

