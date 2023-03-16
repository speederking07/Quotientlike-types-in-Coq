Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.
Require Import Lib.EqDec.

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

Global Instance LO_is_EqDec (A: Type) `{LinearOrder A}: EqDec A.
Proof.
  exists (fun x y => andb (ord x y) (ord y x)). intros x y. 
  destruct (andb (ord x y) (ord y x)) eqn:e; constructor.
  - rewrite Bool.andb_true_iff in e. destruct e. apply anti_sym; auto.
  - intros E. subst. rewrite refl in e. cbn in *. inversion e.
Defined.

Inductive Sorted {A: Type} `{LinearOrder A} : list A -> Prop :=
  | SortedNil : Sorted []
  | SortedSing : forall h: A, Sorted [h]
  | SortedCons : forall h h' : A, forall t: list A,
      Sorted (h' :: t) -> ord h h' = true -> Sorted (h :: h' :: t).

Fixpoint count {A: Type} (p: A -> bool) (l: list A): nat :=
  match l with
  | nil => O
  | cons h t => if p h then S (count p t) else count p t
  end.

Definition permutation {A: Type} (a b : list A) :=
  forall p : A -> bool, count p a = count p b.


Lemma sorted_without_head {A: Type} `{LinearOrder A} : forall l: list A, forall a: A,
  Sorted (a::l) -> Sorted l.
Proof.
  intros l. induction l; intro h.
  - intros _. constructor.
  - intro s. dependent destruction s. assumption.
Qed.

Lemma sorted_with_head {A: Type} `{LinearOrder A} : forall l: list A, forall a h: A,
  Sorted (h::l) -> ord a h = true -> Sorted (a::h::l).
Proof.
  intros l a h sort o. constructor.
  - trivial.
  - assumption.
Qed. 

Lemma sorted_head_relation {A: Type} `{L: LinearOrder A} :
  forall l: list A, forall h: A, Sorted (h::l) -> forall x: A, In x (h :: l) ->
  ord h x = true.
Proof.
  intros l. induction l; intros h sort x H.
  - cbn in H. destruct H.
    + subst. apply refl.
    + contradiction.
  - cbn in H. destruct H.
    + subst. apply refl.
    + assert (ord a x = true).
      { apply IHl.
        - apply (sorted_without_head _ h). assumption.
        - assumption.
      }
      dependent destruction sort; try discriminate.
      apply (trans h a x); assumption.
Qed.

Theorem perm_sym {A: Type} : forall l l': list A, permutation l l' <-> permutation l' l.
Proof.
  intros l l'. unfold permutation. split; intros H p; symmetry; apply (H p).
Qed.

Theorem perm_trans {A: Type} : forall x y z: list A, 
  permutation x y -> permutation y z -> permutation x z.
Proof.
  intros x y z H H0. unfold permutation in *. intro p. specialize (H p). specialize (H0 p).
  transitivity (count p y); assumption.
Qed.

Lemma perm_without_head {A: Type} : forall l l': list A, forall a: A,
  permutation (cons a l) (cons a l') -> permutation l l'.
Proof.
  - intros l l' a H. unfold permutation in *. intro p. specialize (H p). cbn in H.
    destruct (p a).
    + inversion H. reflexivity. 
    + assumption.
Qed.

Lemma perm_with_head {A: Type} : forall l l': list A, forall a: A,
  permutation l l' -> permutation (a::l) (a::l').
Proof.
  intros l l' a perm. unfold permutation in *. intro p. specialize (perm p).
  cbn. destruct (p a).
  - destruct perm. trivial.
  - assumption.
Qed.

Theorem perm_for_element {A: Type} : forall l l': list A, forall x: A,
  permutation l l' -> In x l' -> In x l.
Proof.
  unfold permutation. intros l. induction l; intros l' x perm H.
  - destruct l'.
    + cbn in H. destruct H.
    + specialize (perm (fun x => true)). cbn in perm. discriminate.
  - destruct l'.
    + cbn in H. destruct H.
    + cbn. cbn in H. destruct H.
      * subst. left.
Abort.

Lemma singleton_perm {A: Type} `{L: LinearOrder A} (x y: A) :
   x = y <-> permutation [x] [y].
Proof.
  split.
  - intros [] p. auto.
  - intros perm. specialize (perm (eqf x)). cbn [count] in *. rewrite eqf_refl in perm.
    destruct (eqf x y) eqn:e.
    + rewrite <- eqf_iff in e; auto.
    + inversion perm.
Qed.

Lemma week_eqf_in {A: Type} `{L: EqDec A} :
  forall x: A, forall l: list A, In x l <-> count (eqf x) l <> O.
Proof.
  intros x l. split.
  - intros H. induction l.
    + cbn in H. contradiction.
    + cbn. destruct (eqf x a) eqn:eq.
      * apply PeanoNat.Nat.neq_succ_0.
      * apply IHl. destruct H; auto. subst. rewrite eqf_refl in eq.
        inversion eq.
  - intro H. induction l.
    + cbn in H. contradiction.
    + cbn. destruct (eqf x a) eqn:eq.
      * left. apply eqf_iff. rewrite eqf_sym. assumption.
      * right. apply IHl. cbn in H. rewrite eq in H. assumption.
Qed.

Theorem weak_perm_in {A: Type} `{L: EqDec A} : forall l l': list A, forall x: A,  
  permutation l l' -> In x l' -> In x l.
Proof.
  unfold permutation. intros l l' x perm H. specialize (perm (eqf x)). cut (count (eqf x) l' <> O).
  - intro H0. rewrite <- perm in H0. rewrite week_eqf_in. assumption.
  - apply week_eqf_in. assumption.
Qed.

Lemma sorted_head_eq {A: Type} `{L: LinearOrder A} : forall l l': list A, forall a a': A, 
  permutation (a :: l) (a' :: l') -> Sorted (a :: l) -> Sorted (a' :: l') -> a = a'.
Proof.
  intros l l' h h' perm s1 s2.
  destruct (full h h').
  - assert (In h (h'::l')).
    + apply (weak_perm_in (h'::l') (h :: l) h); try apply perm_sym; auto.
      cbn. left. reflexivity.
    + assert (ord h' h = true) by (apply (sorted_head_relation l' h'); auto).
      apply anti_sym; auto.
  - assert (In h' (h::l)).
    + apply (weak_perm_in (h::l) (h' :: l') h'); auto.
      cbn. left. reflexivity.
    + assert (ord h h' = true) by (apply (sorted_head_relation l h); auto).
      apply anti_sym; auto.
Qed.

(* Unique *)

Theorem sorted_unique_representation {A: Type} `{L: LinearOrder A} :
  forall l l': list A, permutation l l' -> Sorted l -> Sorted l' -> l = l'.
Proof.
  intros l. induction l; intros l' perm sort sort'.
  - destruct l'; auto. specialize (perm (fun _ => true)). cbn in perm. discriminate.
  - destruct l'.
    + specialize (perm (fun _ => true)). cbn in perm. discriminate.
    + assert (a = a0) by (apply (sorted_head_eq l l'); auto). subst.
      f_equal. apply IHl.
      * apply (perm_without_head _ _ a0); auto.
      * apply (sorted_without_head _ a0). auto.
      * apply (sorted_without_head _ a0). auto.
Qed.