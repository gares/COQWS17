From mathcomp Require Import all_ssreflect zmodp. 
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** 
#<div class="slide">#
** Lesson 4

  - Introduction to finite sets
  - Finite graph in SSR
  - Proving Kosaraju's algorithm
#</div>#
----
#<div class="slide">#
  ** Finite sets 

   * In SSR, they are sets over a finite type T
   * a set encapsulates an indicator function {ffun T -> bool}
   * sets share the collective predicate _ \in _ with lists
#<div>#
*)

Definition x0 : 'I_10 := inZp 0.
Definition x1 : 'I_10 := inZp 1.
Definition x2 : 'I_10 := inZp 2.
Definition x3 : 'I_10 := inZp 3.
Definition x4 : 'I_10 := inZp 4.
Definition x5 : 'I_10 := inZp 5.
Definition x6 : 'I_10 := inZp 6.
Definition x7 : 'I_10 := inZp 7.
Definition x8 : 'I_10 := inZp 8.
Definition x9 : 'I_10 := inZp 9.

Definition zs : {set 'I_10} := set0.

Lemma zs0 : x0 \notin zs.
Proof.
rewrite inE.
by [].
Qed.

Definition alls : {set 'I_10} := setT.

Lemma alls0 : x0 \in alls.
Proof.
rewrite inE.
by [].
Qed.

Lemma disjoint_az : [disjoint zs & alls].
Proof.
apply/pred0P.
move=> x.
rewrite /=.
rewrite !inE.
by [].
Qed.

Definition odds := [set x : 'I_10 | odd x].

Lemma odds5 : x5 \in odds.
Proof.
rewrite inE.
by [].
Qed.

Definition evens := x0 |: (x2 |: (x4 |: (x6 |: (x8 |: zs)))).

Lemma oddUeven :  odds :|: evens = alls.
Proof.
apply/setP.
move=> i.
rewrite !inE.
rewrite /=.
case: i.
rewrite /=.
case => //.
by do 9 (case => //).
Qed.
 
Lemma oddIeven :  odds :&: evens = zs.
Proof.
apply/setP.
move=> i.
rewrite !inE.
by case i; do 10 (case => //).
Qed.

(** 
#</div>#
#</div>#
----
#<div class="slide">#
  ** Path 
    - path r x p : r relation, x is an element, p is a list
                   (x :: p) is a path starting at x and ending
                   at (last x p) of r related element
#<div>#
 *)

Fixpoint _path {T : finType} r x (p : seq T) :=
  if p is y :: p' then r x y && _path r y p' else true.

Definition rels := [rel x y : 'I_10 | y == x.+2 :> nat].

Lemma paths0 : path rels x0 [::x2; x4].
Proof.
have pathP := pathP.
have cat_path := cat_path.
have rcons_path := rcons_path.
by [].
Qed.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Graph
   - a graph is manipulated either by its adjacency relation
     or its adjacency function 
   - the functions grel and rgraph let you change representation
#<div>#
*)

Definition nexts :=
   fun x : 'I_10 =>
      if x == x0 then [::x2]
      else if x == x1 then [::x3]
      else if x == x2 then [::x4]
      else if x == x3 then [::x5]
      else if x == x4 then [::x6]
      else if x == x5 then [::x7]
      else if x == x6 then [::x8]
      else if x == x7 then [::x9]
      else [::].

Lemma grels : rels =2 grel nexts.
Proof.
move=> x y.
rewrite /nexts /=.
case: x.
do 8 (case; rewrite /= ?inE //).
move=> x _.
rewrite in_nil.
apply/eqP => H.
have := ltn_ord y.
by rewrite H.
Qed.

Lemma gnexts : forall x, rgraph rels x =i nexts x.
Proof.
have rgraphK := rgraphK. 
move=> x y.
rewrite /rgraph /nexts.
rewrite mem_enum.
rewrite -!topredE /=.
have F : forall x y : 'I_10, (x == y) = (x == y :> nat).
  by move=> x1 y1; apply/eqP/idP => [->//|H]; apply/val_eqP.
case: x.
do 8 (case; rewrite /= ?F; first by case: eqP).
move=> x _.
apply/eqP => H.
have := ltn_ord y.
by rewrite H.
Qed.

(** 
#</div>#
#</div>#
----
#<div class="slide">#
  ** Depth-First Search
     - defs f n x v : 
           returns the nodes visited by a dfs at depth n avoiding the nodes in v
#<div>#
*)

Section Dfs.

Variable T : finType.
Variable g : T -> seq T.

Fixpoint _dfs n (v : seq T) x :=
  if x \in v then v else
  if n is n'.+1 then foldl (_dfs n') (x :: v) (g x) else v.

End Dfs.

Compute [seq nat_of_ord i | i <- dfs nexts 1 [::] x0].
Compute [seq nat_of_ord i | i <- dfs nexts 2 [::] x0].
Compute [seq nat_of_ord i | i <- dfs nexts 3 [::] x0].
Compute [seq nat_of_ord i | i <- dfs nexts 4 [::] x0].
Compute [seq nat_of_ord i | i <- dfs nexts 5 [::] x0].
Compute [seq nat_of_ord i | i <- dfs nexts 6 [::] x0].
Compute [seq nat_of_ord i | i <- dfs nexts 10 [::] x0].
Compute [seq nat_of_ord i | i <- dfs nexts 10 [::] x1].
Compute [seq nat_of_ord i | i <- dfs nexts 10 [::] x2].

(** 
#</div>#
#</div>#
----
#<div class="slide">#
  ** Connection
     - boolean relation that indicates if two nodes are connected 
#<div>#
 *)


Section Connect.

Variable T : finType.
Variable r : rel T.
Definition _connect : rel T := fun x y => y \in _dfs (rgraph r)  #|T| [::] x.

Search connect in fingraph.

End Connect.

(**
#</div>#
#</div>#
----
#<div class="slide">#
  ** Kosaraju's algorithm
    - 2 dfs traversals 
    - one to build a post-fixed stack
    - one on the reverse graph to collect the components
#<div>#
*)

Section Pdfs.

Variable T : finType.
Variable g : T -> seq T.

Fixpoint rpdfs m (p : {set T} * seq T) x :=
  if x \in p.1  then p else 
  if m is m1.+1 then 
     let p1 := foldl (rpdfs m1) (x |: p.1, p.2) (g x) in (p1.1, x :: p1.2)
  else p.

Definition pdfs := rpdfs #|T|.

End Pdfs.

Section Stack.

Variable T : finType.
Variable r : rel T.

Definition stack :=
  (foldl (pdfs (rgraph r)) (set0, [::]) (enum T)).2.

End Stack.

Section Kosaraju.

Variable T : finType.
Variable r : rel T.
Implicit Type p : {set T} * seq (seq T).

Definition kosaraju :=
  let f := pdfs (rgraph [rel x y | r y x]) in 
  (foldl  (fun p x => if x \in p.1 then p else 
                      let p1 := f (p.1, [::]) x in  (p1.1, p1.2 :: p.2))
          (set0, [::]) (stack r)).2.
 
Lemma kosaraju_correct :
    let l := flatten kosaraju in 
 [/\ uniq l, forall i, i \in l &
     forall c : seq T, c \in kosaraju -> 
        exists x, forall y, (y \in c) = (connect r x y && connect r y x)].
Admitted.

End Kosaraju.

(** 
#</div>#
#</div>#

*)

