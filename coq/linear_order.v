Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import Coq.Lists.List.
Import ListNotations.

Set Printing Projections.

Record LinearOrder {A: Type} (ord: A -> A -> bool) := {
  refl : forall x: A, ord x x = true;
  anti_sym : forall x y: A, ord x y = true -> ord y x = true -> x = y;
  trans : forall x y z: A, ord x y = true -> ord y z = true -> ord x z = true;
  full : forall x y, ord x y = true \/ ord y x = true;
}.

Fixpoint leq (x: nat) (y: nat) : bool := 
  match x with
  | O => true
  | S x' => match y with
             | O => false
             | S y' => leq x' y'
             end
  end.

Theorem leq_refl : forall x: nat, leq x x = true.
Proof.
  intro x. induction x.
    cbv. trivial.
    cbn. assumption.
Qed.

Theorem leq_anti_sym : forall x y: nat, leq x y = true -> leq y x = true -> x = y.
Proof.
  intro x. induction x; intro y.
    intros l r. destruct y.
      trivial.
      cbn in r. discriminate.
    intros l r. destruct y.
      cbn in l. discriminate.
      destruct (IHx y).
        cbn in l. assumption.
        cbn in r. assumption.
        trivial.
Qed.

Theorem leq_trans : forall x y z: nat, leq x y = true -> leq y z = true -> leq x z = true.
Proof.
  intros x. induction x; intros y z.
    intros l r. destruct y.
      assumption.
      cbn. trivial.
    destruct y; destruct z; intros l r.
      cbn. trivial.
      cbn in l. discriminate.
      cbn in r. discriminate.
      cbn in *. apply (IHx y z).
        assumption.
        assumption.
Qed.

Theorem leq_full : forall x y: nat, leq x y = true \/ leq y x = true.
Proof.
  intros x. induction x; intros y.
  - left. destruct y; cbn; reflexivity.
  - destruct y.
    + right. cbn. reflexivity.
    + cbn. apply IHx.
Qed.

Theorem leq_is_linear_order : LinearOrder leq.
Proof.
  constructor.
  - apply leq_refl.
  - apply leq_anti_sym.
  - apply leq_trans.
  - apply leq_full.
Qed.