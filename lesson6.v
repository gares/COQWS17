From mathcomp Require Import all_ssreflect  all_algebra.
Open Scope ring_scope.


(** ** The Polynomials
 - Definitions
 - Ring Structure
 - Evaluation
 - Derivative
 - Roots

----
 ** The Polynomials Library : poly.v
 - A  library for univariate polynomials over
 -  ring  structures
 - with extensions for  polynomials whose coefficients range over
 - commutative rings 
 - integral domains

----
** Definition 
 - P = a_n X^n + ... + a_2 X^2 + a_1 X + a_0 
 - list of coefficients (decreasing/increasing  degrees)
 - list of pairs (degree, coef)

 - P = a_0 + a_1 X + a_2 X^2 + ... + a_n X^n
 - A  normalized (i.e. no trailing 0) sequence of coefficients

*)

 Record polynomial (R : ringType) := Polynomial
   {polyseq :> seq R; _ : last 1 polyseq != 0}.


(** ** First properties 
 - Polynomials are coercible to sequences:
 - one can directly take the k_th element of a polynomial
 -  P'_k i.e. retrieve the coefficient of X^k in P.

 - size of a polynomial 
 - the degree of a polynomial is its size minus 1

----
** Notations
 - {poly R}: polynomials over R (a Ring)
 - Poly s : the polynomial built from sequence s
 - 'X : monomial
 - 'X^n : monomial to the power of n
 - a%:P : constant polynomial
 - standard notations of ssralg (+, -, *, *:, ^+)

----
** A polynomial can be defined by extension:
 - poly_(i < n) E i 
 - is the polynomial:
 -  (E 0) + (E 1)  *: 'X + ...  + E (n - 1) *: 'X^(n-1)
----


** Ring Structure
 - addition 
*)
Variable R: ringType.

Definition add_poly (p q : {poly R}) := 
\poly_(i < maxn (size p) (size q)) (p`_i + q`_i).

(*  multiplication  *)

Definition mul_poly (p q : {poly R}) :=
  \poly_(i < (size p + size q).-1)
    (\sum_(j < i.+1) p`_j * q`_(i - j)).

(** ** 
 - The type of polynomials has been equipped
 - with a (commutative / integral) ring structure.

 - All related lemmas of ssralg can be used.

----

** Evaluation
 - (Right-)evaluation of polynomials
 - Warning: type of x 
*)

Fixpoint horner s (x:R) :=
  if s is a :: s'
    then horner s' x * x + a
    else 0.

Notation "p .[ x ]" := (horner p x).


(** ** Properties of coefficients
 - Lifting a ring predicate to polynomials. *)

Definition polyOver (S : pred_class) :=
  [qualify a p : {poly R} | all (mem S) p].

Lemma polyOver_poly (S : pred_class) n E :
  (forall i, (i < n)%N -> E i \in S) -> \poly_(i < n) E i \is a polyOver S.
Admitted.

(** ** polyOver's lemmas:
 - predicate associate to S: at least an addrPred
 -  polyOver0
 - polyOverC 
 -  polyOverX
 - rpred* (from ssralg)

*)
Check polyOver0.


(** ** Derivative
 - definition 
 - notation
 - properties

*)



Definition deriv (p:{poly R}) := 
   \poly_(i < (size p).-1) (p`_i.+1 *+ i.+1).

Local Notation "p ^` ()" := (deriv p).

Fact deriv_is_linear : linear deriv.
Admitted.

Lemma derivM p q : 
(p * q)^`() = p^`() * q + p * q^`().
Admitted.

Definition derivn n p := iter n deriv p.

Check polyOver_deriv.

(** ** Roots
 -  root p x == x is a root of p 

*)
Definition root p : pred R := fun x => p.[x] == 0.

Theorem factor_theorem p a : 
  reflect (exists q, p = q * ('X - a%:P)) 
      (root p a).
Admitted.

Theorem max_poly_roots (p: {poly R}) rs :
  p != 0 -> all (root p) rs -> uniq rs -> 
   (size rs < size p)%N.
Admitted.
