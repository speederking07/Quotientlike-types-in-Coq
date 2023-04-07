Class FullOrd (A: Type) := {
  ord : A -> A -> bool;
  refl : forall x: A, ord x x = true;
  asym : forall x y: A, ord x y = true -> ord y x = true -> x = y;
  full : forall x y: A, ord x y = true \/ ord y x = true;
}.

Record UPair (A: Type) `{FullOrd A} := {
  first: A;
  second: A;
  sorted: ord first second = true;
}.

Arguments first {A _}.
Arguments second {A _}.
Arguments sorted {A}.

Class isHSet (X : Type) :=
  hSet : forall (x y : X) (p q : x = y), p = q.

Lemma bool_is_hset : isHSet bool.
Proof.
  admit.
Admitted.

Print bool.

Definition contains {A: Type} `{FullOrd A} (x y: A) (p: UPair A) :=
  (first p = x /\ second p = y) \/ (first p = y /\ second p = x).

Definition sim {A: Type} `{FullOrd A} (p q: UPair A) :=
  forall x y: A, contains x y p <-> contains x y q. 

Theorem uniqness (A: Type) `{FullOrd A} (p q : UPair A) (x y : A) :
  contains x y p -> contains x y q -> p = q.
Proof.
  intros c1 c2. case_eq (ord x y); intro o;
  destruct p, q; unfold contains in *; cbn in *; 
  destruct c1, c2, H0, H1; subst; 
  try assert (x = y) by (apply asym; assumption);
  subst; try f_equal; try apply bool_is_hset.
Qed.

Theorem uniqness_sim (A: Type) `{FullOrd A} (p q : UPair A) :
  sim p q -> p = q.
Proof.
  unfold sim. intros sim. destruct p. specialize (sim first0 second0).
  apply (uniqness _ _ _ first0 second0); unfold contains in *; cbn in *.
  - left; auto.
  - apply sim. left. auto.
Qed.
  
  

