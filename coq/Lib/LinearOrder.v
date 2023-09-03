Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.

Require Import Master.Lib.EqDec.

Class LinearOrder (A: Type) := {
  ord      : A -> A -> bool;
  refl     : forall x: A, ord x x = true;
  anti_sym : forall x y: A, ord x y = true -> ord y x = true -> x = y;
  trans    : forall x y z: A, ord x y = true -> ord y z = true -> ord x z = true;
  full     : forall x y, ord x y = true \/ ord y x = true;
}.


Lemma ord_false_true (A: Type) `{LinearOrder A} (y x: A) :
  ord x y = false -> ord y x = true.
Proof.
  intros. destruct (full y x); auto. rewrite H0 in H1. inversion H1.
Qed.

Lemma ord_false_trans (A: Type) `{L: LinearOrder A} (z y x: A) :
  ord y x = false -> ord z y = false -> ord z x = false.
Proof. 
  intros H H0. destruct (ord x z) eqn:H1.
  - assert (x <> z).
    + intros [=]. subst. destruct (full y z).
      * rewrite H2 in H. inversion H.
      * rewrite H2 in H0. inversion H0.
    + destruct (ord z x) eqn:H3; auto. exfalso. apply H2. 
      apply (anti_sym x z); auto.
  - assert (ord x z = true).
    + apply (trans x y z); apply ord_false_true; assumption.
    + rewrite H1 in H2. discriminate.
Qed.

Lemma not_full {A: Type} `{LinearOrder A} (x y: A) : ~ (ord x y = false /\ ord y x = false).
Proof.
  intros (a & b). destruct (full x y).
  - rewrite H0 in a. discriminate.
  - rewrite H0 in b. discriminate.
Qed.

Definition comp {A: Type} `{LinearOrder A} (x y: A) : comparison := 
  if ord x y then (if ord y x then Eq else Lt) else Gt.

Lemma comp_eq {A: Type} `{LinearOrder A} (x y: A) : comp x y = Eq <-> x = y.
Proof.
  split.
  - unfold comp. intro C. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2;
    [|inversion C|inversion C|].
    + apply anti_sym; auto.
    + exfalso. apply (not_full x y); split; auto.
  - intros []. unfold comp. rewrite refl. auto.
Qed.

Lemma comp_lt {A: Type} `{LinearOrder A} (x y: A) : 
  comp x y = Lt <-> ord x y = true /\ ord y x = false.
Proof.
 unfold comp. split.
  - intro C. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2;
    [inversion C| auto | inversion C | inversion C].
  - intros (e1 & e2). rewrite e1, e2. auto.
Qed.

Lemma comp_gt {A: Type} `{LinearOrder A} (x y: A) : 
  comp x y = Gt <-> ord x y = false /\ ord y x = true.
Proof.
  unfold comp. split.
  - intro C. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2; 
    [inversion C | inversion C | auto |].
    exfalso. apply (not_full x y); split; assumption.
  - intros (e1 & e2). rewrite e1. auto.
Qed.

Definition comp_inv (c: comparison) : comparison :=
match c with 
| Lt => Gt
| Eq => Eq
| Gt => Lt
end.

Lemma comp_inv_def {A: Type} `{LinearOrder A} (x y: A):
  comp y x = comp_inv (comp x y).
Proof.
  unfold comp. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2; cbn;
  [auto | auto | auto | ].
  exfalso. apply (not_full x y); split; assumption.
Qed.

Lemma comp_inv_iff {A: Type} `{LinearOrder A} (x y: A) (c: comparison):
  comp y x = c <-> comp x y = comp_inv c.
Proof.
  rewrite comp_inv_def. split;
  intro O; destruct c; destruct (comp x y);
  cbn in *; auto; inversion O.
Qed.

Lemma comp_inv_sym (c c': comparison):
  c = comp_inv c' -> comp_inv c = c'.
Proof.
  intros H. destruct c, c'; auto; cbn in *; inversion H.
Qed.

Global Instance LO_is_EqDec (A: Type) `{LinearOrder A}: EqDec A.
Proof.
  exists (fun x y => andb (ord x y) (ord y x)). intros x y. 
  destruct (andb (ord x y) (ord y x)) eqn:e; constructor.
  - rewrite Bool.andb_true_iff in e. destruct e. apply anti_sym; auto.
  - intros E. subst. rewrite refl in e. cbn in *. inversion e.
Qed.

Lemma eqf_comp_not_eq {A: Type} `{LinearOrder A} (x y: A) : comp x y <> Eq <-> eqf x y = false.
Proof.
  rewrite comp_eq. rewrite not_eqf_iff. split; auto.
Qed. 

Lemma eqf_lt{A: Type} `{LinearOrder A} (x y: A) : comp x y = Lt -> eqf x y = false.
Proof.
  intro C. rewrite <-eqf_comp_not_eq. intros C'. rewrite C in C'. inversion C'.
Qed.

Lemma eqf_gt{A: Type} `{LinearOrder A} (x y: A) : comp x y = Gt -> eqf x y = false.
Proof.
  intro C. rewrite <-eqf_comp_not_eq. intros C'. rewrite C in C'. inversion C'.
Qed.