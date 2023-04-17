Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Bool.
Require Import Coq.Program.Equality.
Import ListNotations.
Import PeanoNat.Nat.

Require Import Lib.Deduplicated.
Require Import Lib.Sorted.
Require Import Lib.EqDec.
Require Import Lib.LinearOrder.

Inductive BTree (A: Type) : Type :=
| leaf : BTree A
| node : A -> BTree A -> BTree A -> BTree A.

Arguments leaf {A}.
Arguments node {A} _ _ _.

Definition treeComp {A: Type} `{LinearOrder A} (x: A) (t: BTree A) : option comparison :=
match t with
| leaf => None
| node y _ _ =>  Some (comp x y)
end.

Fixpoint add_tree {A: Type} `{LinearOrder A} (x: A) (t : BTree A) : BTree A :=
match t with
| leaf => node x leaf leaf
| node v l r => match comp x v with
                | Lt => node v (add_tree x l) r
                | Eq => node v l r
                | Gt => node v l (add_tree x r)
                end
end.

Fixpoint to_tree {A: Type} `{LinearOrder A} (l : list A) : BTree A := 
  match l with
  | []      => leaf
  | (x::l') => add_tree x (to_tree l')
  end.

Fixpoint to_list {A: Type} (l : BTree A) : list A := 
  match l with
  | leaf       => []
  | node x l r => to_list l ++ [x] ++ to_list r
  end.

Fixpoint TCount {A: Type}(p: A -> bool)(t: BTree A) : nat :=
  match t with
  | leaf => 0
  | node x l r => if (p x) then S (TCount p l + TCount p r) else TCount p l + TCount p r
  end.

Fixpoint TAny {A: Type}(p: A -> bool)(t: BTree A) : bool :=
  match t with
  | leaf => false
  | node x l r => p x || TAny p l || TAny p r
  end.


Definition BTreeListPermutation {A: Type} (t: BTree A) (l: list A) : Prop :=
  forall p: A->bool, TCount p t = count p l.

Definition BTreePermutation {A: Type} (t1 t2: BTree A) : Prop :=
  forall p: A->bool, TCount p t1 = TCount p t2.

Definition BTreeElem_eq (A: Type) (l l' : BTree A) : Prop := 
  forall p : A -> bool, TAny p l = TAny p l'.

Definition BTreeListElem_eq {A: Type} (t: BTree A) (l: list A) : Prop :=
  forall p : A -> bool, TAny p t = any p l.

Definition dedupSort {A: Type} `{LinearOrder A} (l : list A) : list A :=
  to_list (to_tree l).

 




Lemma to_list_perm {A: Type} (t: BTree A) : BTreeListPermutation t (to_list t).
Proof.
  intros p. induction t; [auto|].
  cbn. rewrite count_list_concat. cbn. destruct (p a).
  - rewrite plus_n_Sm, IHt1, IHt2. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma same_count_TCount {A: Type} (t: BTree A) : forall p: A-> bool,
  TCount p t = count p (to_list t).
Proof.
  apply to_list_perm.
Qed.

Fixpoint TIn {A: Type} (x: A) (t: BTree A) : Prop :=
match t with 
| leaf => False
| node v l r => v = x \/ TIn x l \/ TIn x r
end.

Inductive NormalTree {A: Type} `{LinearOrder A} : BTree A -> Prop :=
| NormLeaf : NormalTree leaf
| NormNode : forall (x: A) (l r: BTree A), NormalTree l -> NormalTree r ->
  (forall y: A, TIn y l -> comp y x = Lt) -> (forall y: A, TIn y r -> comp y x = Gt) ->
  NormalTree (node x l r).

Definition TDeduplicated {A: Type} `{EqDec A} (t: BTree A) : Prop := 
  forall x : A, TIn x t -> TCount (eqf x) t = 1.


Lemma in_to_list {A: Type} (x: A) (t: BTree A) : 
  In x (to_list t) <-> TIn x t.
Proof.
  split.
  - induction t; [auto | cbn].
    intro H. rewrite in_app_iff in H. cbn in *. destruct H as [H | [H | H]].
    + right. left. apply IHt1. assumption.
    + left. assumption.
    + right. right. apply IHt2. assumption.
  - induction t; [auto | cbn].
    intro H. rewrite in_app_iff. cbn. destruct H as [H | [H | H]].
    + right. left. assumption. 
    + left. apply IHt1. assumption.
    + right. right. apply IHt2. assumption.
Qed.





Lemma add_dont_remove {A: Type} `{LinearOrder A} (t : BTree A) (v: A): 
  TIn v t -> forall n: A, TIn v (add_tree n t).
Proof.
  intros I n. induction t; cbn in *; [destruct I|].
  destruct (comp n a) eqn:c.
  - apply I.
  - cbn. destruct I as [e|[l | r]]; subst; auto.
  - cbn. destruct I as [e|[l | r]]; subst; auto.
Qed.

Lemma TIn_add {A: Type} `{LinearOrder A} (n: A) (t : BTree A) (v: A) : 
  TIn v (add_tree n t) <-> n = v \/ TIn v t.
Proof.
  split.
  - intros I. induction t.
    + left. cbn in *. destruct I as [I | [I | I]]; [auto | destruct I | destruct I].
    + cbn in *. destruct (comp n a) eqn:c.
      * rewrite comp_eq in c; subst. cbn in *. destruct I as [e|[l|r]]; subst; auto.
      * cbn in *. destruct I as [e|[l|r]]; subst; auto. destruct (IHt1 l); auto.
      * cbn in *. destruct I as [e|[l|r]]; subst; auto. destruct  (IHt2 r); auto.
  - intros [e | I].
    + subst. induction t; cbn; [auto |].
      destruct (comp v a) eqn:c; cbn; [| auto | auto]. left. symmetry.
      now apply comp_eq.
    + apply add_dont_remove. assumption.
Qed.

Theorem add_preserves_normal {A: Type} `{LinearOrder A} (n: A) (t : BTree A) : 
  NormalTree t -> NormalTree (add_tree n t).
Proof.
  intro N. induction N.
  - cbn. constructor; [constructor| constructor| |]; intros y I; cbn in *; try inversion I.
  - cbn in *. destruct (comp n x) eqn:c.
    + constructor; assumption.
    + constructor; auto. intros y I. rewrite TIn_add in I. destruct I; subst; auto.
    + constructor; auto. intros y I. rewrite TIn_add in I. destruct I; subst; auto.
Qed.

Lemma TCount_for_not_satisfied_pred {A: Type} (t : BTree A) (p: A -> bool): 
  (forall x:A, TIn x t -> p x = false) -> TCount p t = 0.
Proof.
  intros N. induction t; [auto|].
  cbn in *. rewrite (N a); auto. rewrite IHt1, IHt2; auto.
Qed.


(* Deduplicated *)
Theorem normal_is_deduplicated {A: Type} `{LinearOrder A} (t: BTree A) : 
  NormalTree t -> TDeduplicated t.
Proof.
  intro N. induction N; intros y I; cbn in I; [destruct I|].
  destruct I as [e|[I|I]].
  - subst. cbn [TCount]. rewrite eqf_refl, TCount_for_not_satisfied_pred, TCount_for_not_satisfied_pred; auto.
    + intros x I. specialize (H1 x I). rewrite <-eqf_comp_not_eq, comp_inv_iff. cbn. rewrite H1. intros [=].
    + intros x I. specialize (H0 x I). rewrite <-eqf_comp_not_eq, comp_inv_iff. cbn. rewrite H0. intros [=].
  - destruct (comp y x) eqn:c.
    + specialize (H0 y I). rewrite H0 in c. inversion c.
    + cbn [TCount]. rewrite eqf_lt, IHN1, TCount_for_not_satisfied_pred; auto.
      intros z I'. rewrite <-eqf_comp_not_eq, comp_eq. specialize (H1 z I'). intros c'.
      subst. rewrite c in H1. discriminate.
    + cbn [TCount]. rewrite eqf_lt, IHN1, TCount_for_not_satisfied_pred; auto.
      intros z I'. rewrite <-eqf_comp_not_eq, comp_eq. specialize (H1 z I'). specialize (H0 y I).
      intros e. subst. rewrite H1 in H0. discriminate.
  - destruct (comp y x) eqn:c.
    + specialize (H1 y I). rewrite H1 in c. inversion c.
    + cbn [TCount]. rewrite eqf_lt, IHN2, TCount_for_not_satisfied_pred; auto.
      intros z I'. rewrite <-eqf_comp_not_eq, comp_eq. intro e; subst. specialize (H0 z I').
      specialize (H1 z I). rewrite H0 in H1. discriminate.
    + cbn [TCount]. rewrite eqf_gt, IHN2, TCount_for_not_satisfied_pred; auto.
      intros z I'. rewrite <-eqf_comp_not_eq, comp_eq. intro e; subst. specialize (H0 z I'). 
      rewrite c in H0. discriminate.
Qed.

Theorem to_tree_normal {A: Type} `{LinearOrder A} (l: list A) : NormalTree (to_tree l).
Proof.
  induction l; [constructor|]. cbn. apply add_preserves_normal. assumption.
Qed.

Theorem to_tree_dedup {A: Type} `{LinearOrder A} (l: list A) : TDeduplicated (to_tree l).
Proof.
  apply normal_is_deduplicated. apply to_tree_normal.
Qed.

Theorem dedup_dedupSort {A: Type} `{LinearOrder A} (l : list A) : Deduplicated (dedupSort l).
Proof.
  rewrite dup_def_eq. unfold dedupSort, CountDeduplicated. intros x I. rewrite <- same_count_TCount.
  rewrite in_to_list in I. apply to_tree_dedup. assumption.
Qed.



(* Sorted *)
Theorem normal_to_list_sorted {A: Type} `{LinearOrder A} (t: BTree A) : NormalTree t -> Sorted (to_list t).
Proof.
  intros N. induction N; cbn; [constructor|].
  apply concat_sorted; auto.
    + apply head_in_sorted; [auto|]. intros z I. apply comp_gt. apply H1. apply in_to_list. auto.
    + intros z I. apply comp_lt. apply H0. apply in_to_list. auto.
Qed.

Theorem sorted_dedupSort {A: Type} `{LinearOrder A} (l : list A) : Sorted (dedupSort l).
Proof.
  apply normal_to_list_sorted. apply to_tree_normal.
Qed.



(* Preserves elems *)
Lemma to_list_any {A: Type} (t: BTree A) : BTreeListElem_eq t (to_list t).
Proof.
  intros p. induction t; [auto|].
  cbn. rewrite any_concat. cbn. destruct (p a); cbn; auto.
  - rewrite orb_comm. auto.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma add_tree_any {A: Type} `{LinearOrder A} (x: A) (t: BTree A) (p: A -> bool):
  TAny p (add_tree x t) = (if p x then true else TAny p t).
Proof.
  induction t; cbn; [destruct (p x); auto|].
  destruct (comp x a) eqn:e; cbn.
  - rewrite comp_eq in e. subst. destruct (p a) eqn:p_a; auto.
  - rewrite IHt1. destruct (p a); destruct (p x); auto.
  - rewrite IHt2. destruct (p a); destruct (p x); auto. rewrite orb_false_l, orb_comm. auto.
Qed.

Lemma to_tree_any {A: Type} `{LinearOrder A} (l: list A) : BTreeListElem_eq (to_tree l) l.
Proof.
  intros p. induction l; cbn; [auto|].
  rewrite add_tree_any, IHl. auto.
Qed.

Theorem same_elements_dedupSort {A: Type} `{LinearOrder A} (l : list A) : 
  Elem_eq l (dedupSort l).
Proof.
  unfold dedupSort. intros p. rewrite <-to_list_any. symmetry. apply to_tree_any.
Qed.

