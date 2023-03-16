Require Import Bool.
Require Import Setoid.

Class EqDec (A : Type) := { 
  eqf : A -> A -> bool ;
  eqf_leibniz : forall x y: A, reflect (x = y) (eqf x y)
}.

Lemma eqf_refl : forall {A: Type} `{EqDec A}, forall x: A, eqf x x = true.
Proof.
  intros A eq_dec x. destruct (eqf_leibniz x x).
  - reflexivity.
  - exfalso. apply n. reflexivity.
Qed.

Lemma eqf_iff : forall {A: Type} `{EqDec A}, forall x y: A, x = y <-> eqf x y = true.
Proof.
  intros A eq_dec x y. apply reflect_iff. apply eqf_leibniz.
Qed.

Lemma eqf_sym : forall {A: Type} `{EqDec A}, forall x y: A, eqf x y = eqf y x.
Proof.
  intros A eq_dec x y. destruct (eqf x y) eqn:e1; destruct (eqf y x) eqn:e2; auto.
  - rewrite <- eqf_iff in e1. subst. rewrite eqf_refl in e2. inversion e2.
  - rewrite <- eqf_iff in e2. subst. rewrite eqf_refl in e1. inversion e1.
Qed.

Lemma not_eqf_iff : forall {A: Type} `{EqDec A}, forall x y: A, x <> y <-> eqf x y = false.
Proof.
  intros A eq_dec x y. case_eq (eqf x y).
  - intro e. destruct (eqf_leibniz x y).
    + split; intro H; try inversion H; try contradiction.
    + inversion e.
  - intro e. destruct (eqf_leibniz x y).
    + inversion e.
    + split; intro H; assumption. 
Qed.