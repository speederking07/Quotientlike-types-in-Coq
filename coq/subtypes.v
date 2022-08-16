Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.EqdepFacts.

Definition zero (x: nat) : Prop := x = O.

Theorem zero_subtype : forall n m: sig zero, n = m.
Proof.
  intros n m. unfold zero in *. destruct n, m. subst. reflexivity.
Qed.

Lemma one_is_not_zero: 1 <> 0.
Proof.
  intro e. inversion e.
Qed.

Lemma two_is_not_zero: 2 <> 0.
Proof.
  intro e. inversion e.
Qed.

Theorem diffrent_onne_zero : exists n m: sig (fun x => x <> 0), n <> m.
Proof.
  exists (exist _ 1 one_is_not_zero). exists (exist _ 2 two_is_not_zero). intro H.
  inversion H.
Qed.

Record sig' {A: Type} (P: A -> Prop) := {
  val : A;
  sub : P val
}.

Arguments val {A P} _.
Arguments sub {A P} _.

Definition sig_sig' {A: Type} {P: A -> Prop} (x: sig P) : sig' P :=
match x with
| exist _ v p => {| val := v ; sub := p |}
end.

Definition sig'_sig {A: Type} {P: A -> Prop} (x: sig' P) : sig P :=
exist _ (val x) (sub x).

Theorem sig_id : forall A: Type, forall P: A -> Prop, forall x: sig P, sig'_sig (sig_sig' x) = x.
Proof.
  intros A P x. destruct x. unfold sig'_sig. cbn. reflexivity.
Qed.

Theorem sig'_id : forall A: Type, forall P: A -> Prop, forall x: sig' P, sig_sig' (sig'_sig x) = x.
Proof.
  intros A P x. destruct x. cbn. reflexivity.
Qed.

Definition not_K : Prop := exists A: Type, exists x y: A, exists p q: x = y, p <> q.

Definition K := forall {A: Type} (x y: A) (p q: x = y), p = q.




Lemma eq_JMeq : forall (A: Type) (x y: A), x = y -> x ~= y.
Proof.
  intros A x y H. rewrite H. trivial.
Qed.

Lemma not_eq_JMeq : forall (A: Type) (x y: A), x <> y -> x ~= y -> False.
Proof.
  intros A x y H H0. apply H. apply (JMeq_ind (fun z => z = y) eq_refl). apply JMeq_sym. assumption.
Qed.

Print Assumptions   JMeq_eq_dep_id.

Theorem not_unique_sigT : not_K -> exists (A: Type) (P: A -> Type) (x y: sigT P),
  projT1 x = projT1 y /\ x <> y.
Proof.
  unfold not_K.
  intros (A & x & y & p & q & H).
  exists A. exists (fun y => x = y). exists (existT _ y p), (existT _ y q).
  split.
  - cbn. reflexivity.
  - intro e. assert (eq_dep A (eq x) y p y q).
    + apply eq_sigT_eq_dep. assumption.
    + assert (p ~= q) by (apply eq_dep_JMeq; assumption). subst. apply H.  trivial.
Qed.
Print Assumptions  not_unique_sigT.

Print eq_dep.

Definition Irrelevance := forall (P: Prop) (x y: P), x = y.
Require Import Coq.Logic.Eqdep_dec.

Theorem irrelevance_uniqnes : Irrelevance -> forall (A: Type) (P: A -> Prop) (x y: {z: A| P z}),
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros Irr A P [x_v x_p] [y_v y_p] H.
  cbn in H; subst.
  apply eq_dep_eq_sig.
  specialize (Irr (P y_v) x_p y_p); subst.
  constructor.
Qed.

Theorem uniqnes_irrelevance : (forall (A: Type) (P: A -> Prop) (x y: {z: A| P z}),
  proj1_sig x = proj1_sig y -> x = y) -> Irrelevance.
Proof.
  intros Uniq P x y.
  specialize (Uniq unit (fun _ => P) (exist _ tt x) (exist _ tt y) eq_refl). 
  refine (eq_dep_eq_dec (A := unit) _ _).
  - intros. left. destruct x0, y0. reflexivity.
  - apply eq_sig_eq_dep. apply Uniq.
Qed.

Print Assumptions uniqnes_irrelevance.

Class izo (A B: Type) := izo_def {
  f   : A -> B;
  inv : B -> A;
  id1 : forall a: A, inv (f a) = a;
  id2 : forall b: B, f (inv b) = b;
}.





