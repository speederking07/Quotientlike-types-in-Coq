Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Bool.
Import ListNotations.
Import PeanoNat.Nat.
Require Import Lia.

Require Import Lib.EqDec.
Require Import Lib.Sorted.


Inductive Deduplicated {A: Type} : list A -> Prop :=
| DedupNil  : Deduplicated []
| DedupCons : forall (x: A) (l: list A), ~ In x l -> Deduplicated l -> Deduplicated (x::l).

Fixpoint any {A: Type} (p : A -> bool) (l: list A) : bool :=
  match l with
  | [] => false
  | (x::l') => if p x then true else any p l'
  end.

Definition LDeduplicated {A: Type} `{EqDec A} (t: list A) : Prop := 
  forall x : A, In x t -> count (eqf x) t = 1.

Definition Elem_eq {A: Type} (l l' : list A) : Prop := 
  forall p : A -> bool, any p l = any p l'.

Definition Same_elements {A: Type} (l l' : list A) : Prop := 
  forall x : A, In x l <-> In x l'.



Theorem any_in_eq_dec (A: Type) `{E: EqDec A} (l: list A) (x: A) :
  reflect (In x l) (any (eqf x) l).
Proof.
  destruct (any (eqf x) l) eqn:H; constructor.
  - induction l.
    + cbn in *. inversion H.
    + destruct (eqf_leibniz x a); cbn in *.
      * left. symmetry. assumption.
      * right. apply IHl. rewrite (not_eqf_iff x a) in n.
        rewrite n in H. assumption.
  - induction l; auto. intro H0. cbn in *. destruct H0.
    + subst. rewrite eqf_refl in H. inversion H.
    + destruct (eqf x a) eqn:H1; [inversion H|].
      specialize (IHl H H0). auto.
Qed.

Theorem any_in_eq_dec_iff (A: Type) `{E: EqDec A} (l: list A) (x: A) :
  (In x l <-> any (eqf x) l = true).
Proof.
  apply reflect_iff. apply any_in_eq_dec.
Qed.

Lemma in_any_true (A: Type) (l: list A) (x: A) (p : A -> bool) :
  p x = true -> In x l -> any p l = true.
Proof.
  intros P I. induction l; [auto|].
  cbn in I; destruct I.
  - subst; cbn; rewrite P; auto.
  - cbn. destruct (p a); auto.
Qed.

Lemma exist_in_any (A: Type) (l: list A) (p : A -> bool) :
  any p l = true -> exists x: A, p x = true /\ In x l.
Proof.
  intros H. induction l; [inversion H|].
  cbn in *. destruct (p a) eqn:H0.
  - exists a. split; [assumption| left; auto].
  - specialize (IHl H). destruct IHl as (x & (P & I)). exists x.
    split; [| right]; auto.
Qed. 

Lemma forall_in_any (A: Type) (l: list A) (p : A -> bool) : 
  any p l = false -> forall x: A, In x l -> p x = false.
Proof.
  induction l.
  - cbn in *. intros _ x [].
  - intros H x I. cbn in *. destruct (p a) eqn:H0; [inversion H|].
    destruct I; [subst| apply IHl]; auto.
Qed. 

Theorem elem_eq_for_eq_dec (A: Type) `{E: EqDec A} (l l': list A) :
  Elem_eq l l' <-> Same_elements l l'.
Proof.
  unfold Elem_eq, Same_elements. split.
  - intros H x. specialize (H (eqf x)). 
    rewrite any_in_eq_dec_iff, any_in_eq_dec_iff, H. 
    split; intro H0; apply H0.
  - intros H p. destruct (any p l) eqn:e1; destruct (any p l') eqn:e2; auto.
    + destruct (exist_in_any A l p) as (x & (P & H0)); auto.
      rewrite H in H0. assert (p x = false) by (apply (forall_in_any _ l'); auto).
      rewrite P in H1. auto.
    + destruct (exist_in_any A l' p) as (x & (P & H0)); auto.
      rewrite <- H in H0. assert (p x = false) by (apply (forall_in_any _ l); auto).
      rewrite P in H1. auto.
Qed. 


(* Uniquness *) 

Lemma count_for_not_satisfied_pred {A: Type} (l: list A) (p: A->bool) :
  (forall x : A, In x l -> p x = false) -> count p l = 0.
Proof.
  intros N. induction l; auto. cbn. rewrite IHl.
  - rewrite (N a); auto. cbn. left. auto.
  - intros x I. apply (N x). cbn. right. assumption.
Qed.

Lemma count_existing {A: Type} (l: list A) (p: A->bool) (x: A) :
  p x = true -> In x l -> count p l <> O.
Proof.
  intros pred I. induction l; cbn in *; [inversion I|].
  destruct I.
  - subst. rewrite pred. apply neq_succ_0.
  - destruct (p a); auto.
Qed.

Theorem dup_def_eq {A: Type} `{LinearOrder A} (l : list A) : 
  Deduplicated l <-> LDeduplicated l.
Proof.
  unfold LDeduplicated. split.
  - intros D x I. induction D; cbn in I; [inversion I|].
    destruct I.
    + subst. cbn [count]. rewrite eqf_refl, count_for_not_satisfied_pred; auto. 
      intros y I. rewrite <- not_eqf_iff. intros e. subst. apply H0. auto.
    + cbn [count]. rewrite (IHD H1). assert (x <> x0) by (intro e; subst; auto). 
      rewrite not_eqf_iff in H2. rewrite H2. auto.
  - intro D. induction l; constructor.
    + intro I. specialize (D a (or_intror I)). cbn [count] in D.
      rewrite eqf_refl in D. 
      assert (count (eqf a) l <> O) by (apply count_existing with (x := a); auto; apply eqf_refl).
      apply H0. inversion D; auto.
    + apply IHl. intros x I. cbn [count] in *. specialize (D x (or_intror I)).
      destruct (eqf x a) eqn:e; [| auto].
      rewrite <- eqf_iff in e. subst.
      assert (count (eqf a) l <> O) by (apply count_existing with (x := a); auto; apply eqf_refl).
      exfalso. apply H0. inversion D; auto.
Qed.



Definition perm_eqf {A: Type} `{EqDec A} (l l': list A) := 
  forall x: A, count (eqf x) l = count (eqf x) l'.

Lemma perm_eqf_iff {A: Type} `{EqDec A} (l l': list A) : 
  permutation l l' <-> perm_eqf l l'.
Proof.
  split.
  - intros P x. apply (P (eqf x)).
  - revert l'. induction l; intros l' E p.
    + destruct l'; auto. specialize (E a). cbn in E. rewrite eqf_refl in E. inversion E.
    + rewrite (remove_perm' a l l'); auto.
      * rewrite in_count_not_O. specialize (E a). rewrite <- E. cbn. rewrite eqf_refl. auto.
      * intros p'. apply IHl. intros x. specialize (E x). cbn in *. destruct (eqf x a) eqn:e.
        -- apply eq_add_S. rewrite E. rewrite (remove_count_true a); auto.
           rewrite <- eqf_iff in e. subst. rewrite in_count_not_O. rewrite <-E. auto.
        -- rewrite E. rewrite (remove_count_false a); auto.
Qed.

Lemma any_count_true {A: Type} (l: list A) (p: A -> bool) :
  (count p l <> 0) <-> (any p l = true).
Proof.
  split; intro H.
  - induction l.
    + cbn in *. contradiction.
    + cbn in *. destruct (p a) eqn: e; auto.
  - intro C. induction l.
    + cbn in *. discriminate.
    + cbn in *. destruct (p a) eqn: e; try discriminate. apply IHl; auto.
Qed.

Lemma any_count_false {A: Type} (l: list A) (p: A -> bool) :
  (count p l = 0) <-> (any p l = false).
Proof.
  split; intro H.
  - induction l; auto. cbn in *. destruct (p a) eqn: e; auto; try discriminate.
  - induction l; auto. cbn in *. destruct (p a) eqn: e; auto; try discriminate.
Qed.

Theorem unique_dedup_perm {A: Type} `{LinearOrder A} (l l': list A) : 
  Elem_eq l l' -> Deduplicated l -> Deduplicated l' -> permutation l l'.
Proof.
  rewrite dup_def_eq, dup_def_eq. rewrite perm_eqf_iff.
  unfold Elem_eq, LDeduplicated. intros eq d1 d2 x.
  specialize (eq (eqf x)). destruct (any (eqf x) l) eqn:I1; destruct (any (eqf x) l') eqn:I2; try discriminate.
  - rewrite <- any_count_true in I1. rewrite <- any_count_true in I2.
    rewrite <- in_count_not_O in I1. rewrite <- in_count_not_O in I2. rewrite d1, d2; auto. 
  - rewrite <- any_count_false in I1. rewrite <- any_count_false in I2. rewrite I1, I2. auto.
Qed.

Theorem deduo_sort_uniquenss {A: Type} `{LinearOrder A} (l l': list A) : Elem_eq l l' -> 
  Sorted l -> Sorted l' -> Deduplicated l -> Deduplicated l' -> l = l'.
Proof.
  intros e_eq s1 s2 d1 d2. apply unique_sorted; auto. apply unique_dedup_perm; auto.
Qed.