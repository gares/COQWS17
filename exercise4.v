From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Kosaraju.

Variable T : finType.
Implicit Types s : {set T}.
Implicit Types l : seq T.
Implicit Types A B C : pred T.
Implicit Types x y z : T.

(** Some basic facts about disjoint where the first element is a set
    and the second one a list *)
Section Lib.

Lemma disjoint_setU s1 s2 A  :
   [disjoint s1 :|: s2 & A] = [disjoint s1 & A] && [disjoint s2 & A].
Proof.
(*D*)by rewrite -(@eq_disjoint _ [predU s1 & s2]) ?disjointU // => x; rewrite !inE.
(*A*)Qed.

Lemma disjoint_setUr s1 s2 A :
   [disjoint A & s1 :|: s2] = [disjoint A & s1] && [disjoint A & s2].
Proof.
(*D*)by rewrite disjoint_sym disjoint_setU !(disjoint_sym A).
(*A*)Qed.

Lemma disjoint_catr l1 l2 A :
       [disjoint A & l1 ++ l2 ] = [disjoint A & l1] && [disjoint A & l2].
Proof.
(*D*)rewrite -(@eq_disjoint_r _ [predU l1 & l2]); last by move=> x; rewrite inE mem_cat.
(*D*)by rewrite disjoint_sym disjointU disjoint_sym (disjoint_sym (mem l2)).
(*A*)Qed.

Lemma disjoint_set1 x A : [disjoint [set x] & A] = (x \notin A).
Proof.
(*A*)Qed.

Lemma disjoint_setU1 x s A :
   [disjoint x |: s & A] = (x \notin A) && [disjoint s & A].
Proof.
(*A*)Qed.

Lemma disjoint_setU1r x s A :
   [disjoint A & x |: s] = (x \notin A) && [disjoint A & s].
Proof.
(*A*)Qed.
 
Lemma disjoint_consr x l A :
   [disjoint A & x :: l] = (x \notin A) && [disjoint A & l].
Proof.
(*A*)Qed.

Lemma disjoint_transr A B C :
   B \subset C -> [disjoint A & C] -> [disjoint A & B].
Proof.  
(*A*)Qed.

End Lib.

Section Stack.

Section Rconnect.

Variable r : rel T.

(** x is connected to y avoiding elements of l *)
Definition rconnect s := 
   connect [rel x y | (r x y) && (y \notin s)].

Local Notation "x -[ s ]-> y" := (rconnect s x y) 
  (at level 10, format "x  -[ s ]->  y").

Local Notation "x -[]-> y" := (rconnect set0 x y) 
  (at level 10, format "x  -[]->  y").

Lemma path_relE s x p : 
  path [rel x y | (r x y) && (y \notin s)] x p = path r x p && [disjoint p & s].
Proof.
(*A*)Qed.

Lemma rconnectP s x y :
   reflect 
    (exists2 p, path r x p & ((y = last x p) /\ [disjoint p & s]))
    (x -[s]-> y).
Proof.
(*A*)Qed.

Lemma rconnect_set0  : rconnect set0 =2 connect r.
Proof.
(*A*)Qed.

Lemma rconnect_ref s : reflexive (rconnect s).
Proof. 
(*A*)Qed.

Lemma rconnect1 s x y : y \notin s -> r x y -> x -[s]-> y.
Proof.
(*A*)Qed.

Lemma rconnect_trans s : transitive (rconnect s).
Proof. 
(*A*)Qed.

Lemma rconnect_subset (s1 s2 : {set T}) x y : 
  {subset s1 <= s2} ->  x -[s2]-> y -> x -[s1]-> y.
Proof.
(*A*)Qed.

Lemma rconnect_setU s1 s2 x y : 
  [disjoint [set z | x -[s1]-> z && z -[s1]-> y] & s2] ->
  x -[s1]-> y ->  x -[s2 :|: s1]-> y.
Proof.
(*A*)Qed.

Lemma rconnect_setU1r s x y z :
  ~~ z -[s]-> y ->  x -[s]-> y -> x -[z |: s]-> y.
Proof.
(*A*)Qed.

Lemma rconnect_setU1l s x y z : 
  ~~ (x -[s]-> z) ->  x -[s]-> y -> x -[z |: s]-> y.
Proof.
(*A*)Qed.

Lemma rconnect_id_setU1 s x y : x -[x |: s]-> y = x -[s]-> y.
Proof.
(*A*)Qed.

(** x is biconnected to y avoiding the elements of s *)
Definition requiv s x y  :=  x -[s]-> y && y -[s]-> x.

Local Notation "x =[ s ]= y" := (requiv s x y) 
  (at level 10, format "x  =[ s ]=  y").

Local Notation "x =[]= y" := (requiv set0 x y) 
  (at level 10, format "x  =[]=  y").

Lemma requiv_set0 : requiv set0 =2 (fun x y => connect r x y && connect r y x).
Proof.
(*A*)Qed.

Lemma requiv_ref s : reflexive (requiv s).
Proof.
(*A*)Qed.

Lemma requiv_sym s : symmetric (requiv s).
Proof.
(*A*)Qed.

Lemma requiv_trans s : transitive (requiv s).
Proof.
(*A*)Qed.

Lemma lrequiv_subset s1 s2 x y : {subset s1 <= s2} -> x =[s2]= y -> x =[s1]= y.
Proof.
(*A*)Qed.

(** Canonical element in a list : find the first element of l1
   that is equivalent to x avoiding l2 *)
Definition rcan x p := nth x p.2 (find (requiv p.1 x) p.2).

Notation "C[ x ]_ p" := (rcan x p) 
  (at level 9, format "C[ x ]_ p").

Lemma mem_rcan x p : x \in p.2 -> C[x]_p \in p.2.
Proof.
(*A*)Qed.

Lemma rcan_cons x y s l : 
  C[x]_(s, y :: l) =  if x =[s]= y then y else C[x]_(s,l).
Proof.
(*A*)Qed.

Lemma rcan_cat x s l1 l2 : x \in l1 -> C[x]_(s, l1 ++ l2) = C[x]_(s, l1).
Proof.
(*A*)Qed.

Lemma requiv_can x s l : x \in l -> C[x]_(s, l) =[s]= x.
Proof.
(*A*)Qed.

(* x occurs before y in l *)
Definition before l x y  := index x l <= index y l.

Lemma before_filter_inv a x y l (l1 := [seq i <- l | a i]) :
  x \in l1 -> y \in l1 -> before l1 x y -> before l x y.
Proof.
(*A*)Qed.

Lemma before_filter x y l a (l1 := [seq i <- l | a i]) :
  x \in l1 -> before l x y -> before l1 x y.
Proof.
(*A*)Qed.

Lemma leq_index_nth x l i : index (nth x l i) l  <= i.
Proof.
(*A*)Qed.

Lemma index_find x l a :  has a l -> index (nth x l (find a l)) l = find a l.
Proof.
(*A*)Qed.

Lemma before_can x  y s l : 
  x \in l -> y \in l -> x =[s]= y -> before l C[x]_(s, l) y.
Proof.
(*A*)Qed.

Lemma before_canW x s1 s2 l : 
 x \in l -> {subset s1 <= s2} -> before l C[x]_(s1, l) C[x]_(s2, l).
Proof.
(*A*)Qed.

(** well formed list : rconnected elements are inside and
                      canonical elements are on top *)
Definition rwf (p : {set T} * seq T) := 
  [disjoint p.1 & p.2] /\
 forall x y , 
   x \in p.2 -> x -[p.1]-> y -> y \in p.2 /\ before p.2 C[x]_p y.

Local Notation "W_[ s ] l" := (rwf (s, l)) (at level 10).
Local Notation "W_[] l " := (rwf (set0,l)) (at level 10).

Lemma rwf_nil s : W_[s] [::].
Proof. 
(*A*)Qed.

(** Removing the equivalent elements of the top preserve well-formedness *)
Lemma rwf_inv x s l : 
  W_[s] (x :: l) -> W_[s] [seq y <- x :: l | ~~ x =[s]= y].
Proof.
apply: ok.
Qed.

(** Computing the connected elements for the reversed graph gives
   the equivalent class of the top element of an well_formed list *)
Lemma rwf_equiv x y s l : 
  W_[s] (x :: l) -> x =[s]= y = (y \in (x :: l)) && y -[s]-> x.
Proof.
(*A*)Qed.

(** Computing well_formed list by accumulation *)
Lemma rwf_cat s1 l1 l2 : W_[s1] l1 -> W_[s1 :|: [set x in l1]] l2 -> W_[s1] (l2 ++ l1).
Proof.
(*A*)Qed.

Lemma rwf_setU1_l x s l : x \notin l ->  W_[s] l -> W_[x |: s] l.
Proof.
(*A*)Qed.

(** Computing well_formed list by accumulation *)
Lemma rwf_cons_r x s l :
 (forall y, y \in l -> x -[s]-> y) ->
 (forall y, r x y -> y \notin x |: s -> y \in l) ->
  x \notin s -> W_[x |: s] l ->  W_[s] (x :: l).
Proof.
(*A*)Qed.

End Rconnect.

Variable r : rel T.

Local Notation "x -[ l ]-> y" := (rconnect r l x y) 
  (at level 10, format "x  -[ l ]->  y").
Local Notation "x -[]-> y" := (rconnect r [::] x y) 
  (at level 10, format "x  -[]->  y").
Local Notation "x =[ l ]= y" := (requiv r l x y) 
  (at level 10, format "x  =[ l ]=  y").
Local Notation "x =[]= y" := (requiv r [::] x y) 
  (at level 10, format "x  =[]=  y").
Local Notation "W_[ l1 ] l2 " := (rwf r (l1, l2)) (at level 10).
Local Notation "W_[] l" := (rwf r (set0, l)) (at level 10).

Section Pdfs.

Variable g : T -> seq T.

Fixpoint rpdfs m (p : {set T} * seq T) x :=
  if x \in p.1  then p else 
  if m is m1.+1 then 
     let p1 := foldl (rpdfs m1) (x |: p.1, p.2) (g x) in (p1.1, x :: p1.2)
  else p.

Definition pdfs := rpdfs #|T|.

End Pdfs.

Lemma pdfs_correct (p : {set T} * seq T) x :
  let (s, l) := p in 
  uniq l /\  {subset l <= s} ->
  let p1 := pdfs (rgraph r) p x in
  let (s1, l1) := p1 in
  if x \in s then p1 = p else
       [/\ #|s| <= #|s1| & uniq l1]
    /\
       exists l2 : seq T,
       [/\ x \in l2, s1 = s :|: [set y in l2], l1 = l2 ++ l, W_[s] l2 &
           forall y, y \in l2 -> x -[s]-> y].
Proof.
(*D*)apply: ok.
(*A*)Qed.

Lemma pdfs_connect s x : 
  x \notin s ->
  let (s1, l1) := pdfs (rgraph r) (s, [::]) x in
  [/\ uniq l1, s1 = s :|: [set x in l1], [disjoint s & l1] & 
      forall y, y \in l1 = x -[s]-> y].
Proof.
(*A*)Qed.

(** Building the stack of all nodes *)
Definition stack :=
  (foldl (pdfs (rgraph r)) (set0, [::]) (enum T)).2.

(** The stack is well-formed and contains all the nodes *)
Lemma stack_correct : W_[] stack /\ forall x, x \in stack.
Proof.
(*A*)Qed.

Lemma rconnect_rev l s1 s2 x y : 
     {subset s1 <= s2} -> [disjoint s2 & x :: l] ->
     (forall z, z \in s2 :|: [set t in x :: l]) ->
     W_[s1] (x :: l) ->
     ((y \in x :: l) && y -[s1]-> x) = (rconnect [rel x y | r y x] s2 x y).
Proof.
(*A*)Qed.

End Stack.

Variable r : rel T.

(** Kosaraju algorithm *)
Definition kosaraju :=
  let f := pdfs (rgraph [rel x y | r y x]) in 
  (foldl  (fun (p : {set T} * seq (seq T)) x => if x \in p.1 then p else 
                      let p1 := f (p.1, [::]) x in  (p1.1, p1.2 :: p.2))
          (set0, [::]) (stack r)).2.

Lemma kosaraju_correct :
    let l := flatten kosaraju in 
 [/\ uniq l, forall i, i \in l &
     forall c : seq T, c \in kosaraju -> 
        exists x, forall y, (y \in c) = (connect r x y && connect r y x)]. 
Proof.
(*A*)Qed.

End Kosaraju.


