Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.
Import ListNotations.

Require Import Lib.LinearOrder.
Require Import Lib.EqDec.



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


(* Remove *)
Fixpoint remove {A: Type} `{EqDec A} (x: A) (l: list A) :=
match l with 
| []     => []
| (h::t) => if eqf x h then t else h :: remove x t
end.

Lemma remove_count_true {A: Type} `{EqDec A} (h: A) (l: list A) (p: A -> bool) :
  In h l -> p h = true -> count p l = S (count p (remove h l)).
Proof.
  induction l; intros I t; cbn in *; destruct I.
  - subst. rewrite t, eqf_refl. auto.
  - destruct (p a) eqn:e; destruct (eqf h a) eqn:e1; [auto|..].
    + cbn in *. rewrite e, IHl; auto.
    + rewrite <- eqf_iff in e1. subst. rewrite t in e. discriminate.
    + cbn in *. rewrite e, IHl; auto.
Qed.

Lemma remove_count_false {A: Type} `{EqDec A} (h: A) (l: list A) (p: A -> bool) :
  p h = false -> count p l = count p (remove h l).
Proof.
  induction l; intros f; auto. cbn in *. 
  destruct (p a) eqn:e; destruct (eqf h a) eqn:e1; [| |auto|].
  - rewrite <- eqf_iff in e1. subst. rewrite f in e. discriminate.
  - cbn. rewrite e. f_equal. apply IHl; auto.
  - cbn. rewrite e, IHl; auto.
Qed.

Lemma in_count_not_O {A: Type} `{EqDec A} (l: list A) (x: A) :
  In x l <-> count (eqf x) l <> O.
Proof.
  split.
  - intros I. induction l; cbn in *; destruct I.
    + subst. rewrite eqf_refl. auto.
    + destruct (eqf x a) eqn: e; auto.
  - intros C. induction l; cbn in *; [contradiction|].
    destruct (eqf x a) eqn: e; auto. rewrite <- eqf_iff in e.
    subst. left. auto.
Qed.

Lemma perm_in {A: Type} `{EqDec A} (l l': list A) (x: A) :
  permutation l l' -> In x l -> In x l'.
Proof.
  intros perm I. rewrite in_count_not_O. rewrite in_count_not_O in I.
  specialize (perm (eqf x)). rewrite <-perm. assumption.
Qed.

Lemma remove_perm {A: Type} `{EqDec A} (h: A) (l l': list A) :
  permutation (h :: l) l' -> permutation l (remove h l').
Proof.
  unfold permutation. revert l'. induction l; intros l' perm p.
  - assert (In h l') by (apply (perm_in [h]); auto; cbn; auto).
    cbn. apply eq_add_S. specialize (perm p). cbn in *. destruct (p h) eqn:e.
    + rewrite <-remove_count_true; auto.
    + rewrite <-remove_count_false; auto.
  - assert (In h l') by (apply (perm_in (h::a::l)); cbn; auto).
    assert (In a l') by (apply (perm_in (h::a::l)); cbn; auto).
    cbn. apply eq_add_S. apply eq_add_S. specialize (perm p). cbn in *.
    destruct (p h) eqn:e.
    + rewrite <-remove_count_true; auto.
    + rewrite <-remove_count_false; auto.
Qed.

Lemma remove_perm' {A: Type} `{EqDec A} (h: A) (l l': list A) :
  In h l' -> permutation l (remove h l') -> permutation (h :: l) l' .
Proof.
  unfold permutation. induction l; intros I perm p.
  - cbn in *. specialize (perm p). destruct (p h) eqn: e.
    + rewrite (remove_count_true h); auto.
    + rewrite (remove_count_false h); auto.
  - cbn in *. specialize (perm p). destruct (p h) eqn: e.
    + rewrite (remove_count_true h l'); auto.
    + rewrite (remove_count_false h l'); auto.
Qed.



(* Sorted lemmas *)
Lemma count_list_concat {A: Type} (l l': list A): 
  forall p: A-> bool, count p (l ++ l') = count p l + count p l'.
Proof.
  intros p. induction l; [auto|].
  cbn. destruct (p a); rewrite IHl; auto.
Qed.

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

Lemma head_in_sorted {A: Type} `{LinearOrder A} (h: A) (l: list A) : Sorted l -> 
  (forall x: A, In x l -> ord h x = true) -> Sorted (h::l).
Proof.
  intros s N. induction l; constructor; [auto|]. apply N. cbn. auto.
Qed. 

Lemma concat_sorted {A: Type} `{LinearOrder A} (h: A) (l l': list A) : Sorted l -> Sorted (h :: l') -> 
  (forall x: A, In x l -> ord x h = true) -> Sorted (l ++ (h :: l')).
Proof.
  intros s1 s2 N. induction l; [auto | destruct l]; cbn.
  + constructor; [auto | ]. apply (N a). cbn. auto.
  + cbn in *. constructor.
    * apply IHl.
      -- apply (sorted_without_head _ a). assumption.
      -- intros x I. apply N. auto.
    * dependent destruction s1. assumption.
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