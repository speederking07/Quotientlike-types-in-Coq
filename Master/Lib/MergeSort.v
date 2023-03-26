Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import PeanoNat.
Import Nat.

Require Import Lib.LinearOrder.
Require Import Lib.Sorted.

Inductive BT(A : Type) : Type :=
  | leaf : A -> BT A
  | node : BT A -> BT A -> BT A.

Arguments leaf {A}.
Arguments node {A}.

Fixpoint BTInsert {A : Type} (x : A) (tree : BT A) :=
  match tree with
  | leaf y => node (leaf x)(leaf y)
  | node l r => node r (BTInsert x l)
  end.

Fixpoint BTSize{A : Type}(tree : BT A) :=
  match tree with
  | leaf y => 1
  | node l r => BTSize l + BTSize r
  end.

Fixpoint listToBT{A : Type}(x : A)(list : list A): BT A :=
  match list with
  | nil => leaf x
  | cons y list' => BTInsert x (listToBT y list')
  end.

Fixpoint merge {A : Type} (ord : A -> A -> bool) (l1 : list A): (list A) -> list A :=
  match l1 with
  | [] => fun (l2 : list A) => l2
  | h1::t1 => fix anc (l2 : list A) : list A :=
    match l2 with
    | [] => l1
    | h2::t2 => if ord h1 h2 
                then h1::(merge ord t1) l2
                else h2::anc t2
    end
  end.

Fixpoint BTSort {A : Type} (ord : A -> A -> bool) (t : BT A): list A :=
  match t with
  | leaf x => [x]
  | node l r => merge ord (BTSort ord l) (BTSort ord r)
  end. 

Definition mergeSort {A: Type} (ord : A -> A -> bool) (l: list A): list A :=
  match l with
  | [] => []
  | x::l' => BTSort ord (listToBT x l')
  end.

Fixpoint BTToList{A: Type}(t: BT A) : list A :=
  match t with
  | leaf a => [a]
  | node l r => (BTToList l) ++ (BTToList r)
  end.


(* Perm def *)
Fixpoint BTCount {A: Type} (p: A -> bool) (t: BT A) :=
  match t with
  | leaf x => if p x then 1 else 0
  | node l r => BTCount p l + BTCount p r
  end.

Definition BTListPermutation{A: Type}(t: BT A)(l: list A) : Prop :=
  forall p: A->bool, BTCount p t = count p l.

Definition BTPermutation{A: Type}(t1 t2: BT A) : Prop :=
  forall p: A->bool, BTCount p t1 = BTCount p t2.

Lemma merge_perm {A: Type} (p: A->bool) (ord: A->A->bool) (l1 l2 : list A) :
  count p l1 + count p l2 = count p (merge ord l1 l2).
Proof.
  revert l2. induction l1; intros l2; auto.
  induction l2.
  - cbn. rewrite add_0_r. trivial.
  - cbn. destruct (ord a a0).
    + destruct (ord a0 a); cbn; destruct (p a); cbn;
      f_equal; rewrite <- IHl1; auto.
    + destruct (ord a0 a); cbn in *; destruct (p a0);
      try rewrite Nat.add_succ_r; try f_equal;
      rewrite <- IHl2; auto.
Qed.

Lemma BTSort_is_perm (A:Type) (ord: A->A->bool) (t : BT A) (p: A->bool) :
  BTCount p t = count p (BTSort ord t).
Proof.
  revert p. induction t; intro p; auto. cbn.
  rewrite IHt1, IHt2, <- merge_perm. auto.
Qed.

Lemma BT_insert_count (A : Type) (p: A->bool) (x : A) (t : BT A):
  BTCount p (BTInsert x t) = if p x then S (BTCount p t) else BTCount p t.
Proof.
  induction t; cbn.
  - destruct (p x), (p a); auto.
  - rewrite IHt1. destruct (p x); cbn.
    1: rewrite add_succ_r; f_equal.
    1-2: rewrite add_comm; auto. 
Qed.

Lemma BTSort_perm (A: Type) (ord: A->A->bool) (l : list A) (x: A) :
   permutation (x::l) (BTSort ord (listToBT x l)).
Proof.
  revert x. induction l; intro x; cbn; try constructor.
  unfold permutation in *. intros p. rewrite <- BTSort_is_perm.
  rewrite BT_insert_count. cbn. destruct (p x) eqn:e.
  1: f_equal.
  1-2: cbn in *; rewrite IHl, <- BTSort_is_perm; auto.
Qed.


Lemma merged_sorted_lists (A: Type) `{lo: LinearOrder A} (l1 l2: list A) :
  Sorted l1 -> Sorted l2 -> Sorted (merge ord l1 l2).
Proof.
  intros s1. revert l2. induction s1; auto.
  - intros l2 s2. induction s2; cbn; try constructor.
    + destruct (ord h h0) eqn:o; constructor; try constructor; auto.
      apply ord_false_true. auto.
    + cbn. destruct (ord h h0) eqn:o.
      * assert (ord h h' = true) by (apply (trans h h0 h'); auto).
        cbn in IHs2. rewrite H0 in IHs2. 
        constructor; try constructor; [dependent destruction IHs2 | | ]; auto.
      * cbn in IHs2. destruct (ord h h') eqn:o2; constructor; auto.
        apply ord_false_true; auto.
  - intros l2 s2. induction s2.
    + cbn. constructor; auto.
    + specialize (IHs1 [h0]). cbn in *. destruct (ord h' h0) eqn:o1.
      * assert (ord h h0 = true) by (apply (trans _ h' _); auto).
        rewrite H0. constructor; auto. apply IHs1. constructor.
      * destruct (ord h h0) eqn:o2; constructor; auto.
        -- apply IHs1; constructor.
        -- constructor; auto.
        -- apply ord_false_true; auto.
    + destruct (ord h h0) eqn:o1.
      * specialize (IHs1 (h0 :: h'0 :: t1)). cbn. rewrite o1.
        destruct (ord h' h0) eqn:o2; constructor; auto.
        1-2: cbn in IHs1; rewrite o2 in IHs1; apply IHs1; constructor; auto.
      * cbn in *. rewrite o1. destruct (ord h h'0) eqn:o2; constructor; auto.
        apply ord_false_true; assumption.
Qed.

Lemma BT_sorts (A: Type) `{lo: LinearOrder A} (t: BT A) : Sorted (BTSort ord t).
Proof.
  induction t; cbn.
  - constructor.
  - apply merged_sorted_lists; assumption.
Qed.

Theorem mergeSort_is_sorted (A: Type) `{lo: LinearOrder A} (l: list A):
  Sorted (mergeSort ord l).
Proof.
  induction l; cbn; try constructor. now apply BT_sorts.
Qed.

Theorem mergeSort_is_perm (A: Type) `{lo: LinearOrder A} (l: list A):
  permutation l (mergeSort ord l).
Proof.
  induction l; cbn.
  - unfold permutation. intro. cbn. reflexivity.
  - now apply BTSort_perm.
Qed.

Theorem merge_sort_idempotent (A: Type) `{lo: LinearOrder A} (l: list A):
  (mergeSort ord l) = (mergeSort ord (mergeSort ord l)).
Proof.
  apply sorted_unique_representation; auto.
  - apply mergeSort_is_perm.
  - apply mergeSort_is_sorted.
  - apply mergeSort_is_sorted.
Qed.

