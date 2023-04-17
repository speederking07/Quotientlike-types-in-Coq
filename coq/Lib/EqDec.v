Require Import Bool.
Require Import Setoid.
Require Import Coq.Lists.List.
Import PeanoNat.Nat.
Import ListNotations.

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

Fixpoint list_eq {A: Type} `{EqDec A} (l l': list A) : bool :=
match l, l' with
| []      , []         => true
| (h :: t), (h' :: t') => if eqf h h' then list_eq t t' else false
| _       , _          => false
end.

Global Instance EqDec_for_list (A: Type) `{EqDec A}: EqDec (list A).
Proof.
  exists list_eq. intros x y. destruct (list_eq x y) eqn:e.
  - constructor. revert e. revert y. induction x; intros y e.
    + destruct y; [auto|]. cbn in e. inversion e.
    + destruct y; cbn in *; [inversion e|]. destruct (eqf a a0) eqn:eq; [|inversion e].
      rewrite <-eqf_iff in eq. subst. f_equal. apply IHx; auto.
  - constructor. revert e. revert y. induction x; intros y e e'; subst.
    + cbn in e. inversion e.
    + cbn in *. rewrite eqf_refl in e. apply (IHx x); auto.
Defined.

Global Instance EqDec_for_nat : EqDec nat.
Proof.
  exists (fun x y => x =? y). intros x y. destruct (x =? y) eqn:e.
  - constructor. apply eqb_eq. auto.
  - constructor. apply eqb_neq. auto.
Defined.


Global Program Instance Unit_for_EqDec : EqDec unit := {
  eqf := fun _ _ => true;
}.

Next Obligation. constructor. destruct x, y. auto. Defined.

