Definition Fun_ex := forall (A B : Type) (f g: A -> B), f = g <-> (forall x: A, f x = g x).

Definition Prop_ex := forall (P Q : Prop), (P <-> Q) -> P = Q.

Definition K := forall (A: Type) (x y : A) (p q : x = y), p = q.

Definition Irrelevance := forall (P: Prop) (x y: P), x = y.


Theorem ok : Prop_ex -> K -> Irrelevance.
Proof.
  unfold Prop_ex, K, Irrelevance.
  intros Prop_ex K P x y. 
  assert (P = (P = True)).
  - apply Prop_ex. split.
    + intros z. rewrite (Prop_ex P True); trivial. split.
      * trivial.
      * intros _. assumption.
    + intros []. assumption.
  - revert x y. rewrite H. apply K.
Qed. 