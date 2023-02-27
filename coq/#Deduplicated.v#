Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Bool.
Require Import Coq.Program.Equality.
Import ListNotations.
Import PeanoNat.Nat.

Print In.
Print reflect.

Inductive Deduplicated {A: Type} : list A -> Prop :=
| DedupNil  : Deduplicated []
| DedupCons : forall (x: A) (l: list A), ~ In x l -> Deduplicated l -> Deduplicated (x::l).

Fixpoint any {A: Type} (p : A -> bool) (l: list A) : bool :=
  match l with
  | [] => false
  | (x::l') => if p x then true else any p l'
  end.

Definition Elem_eq {A: Type} (l l' : list A) : Prop := 
  forall p : A -> bool, any p l = any p l'.

Definition Same_elements {A: Type} (l l' : list A) : Prop := 
  forall x : A, In x l <-> In x l'.

Class EqDec (A : Type) := { 
  eqf : A -> A -> bool ;
  eqf_leibniz : forall x y: A, reflect (x = y) (eqf x y)
}.

Print Bool.

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

Theorem any_in_eq_dec : forall (A: Type) `{EqDec A}, forall l: list A, forall x: A,
  reflect (In x l) (any (eqf x) l).
Proof.
  intros A eq_dec l x. case_eq (any (eqf x) l).
  - intro H. constructor. induction l.
    + cbn in *. inversion H.
    + destruct (eqf_leibniz x a).
      * cbn. left. symmetry. assumption.
      * cbn in *. right. apply IHl. rewrite (not_eqf_iff x a) in n.
        rewrite n in H. assumption.
  - intro H. constructor. induction l.
    + cbn. auto.
    + intro H0. cbn in *. destruct H0.
      * destruct H0. rewrite (eqf_refl a) in H. inversion H.
      * case_eq (eqf x a); intro H1.
        -- rewrite H1 in H. inversion H.
        -- rewrite H1 in H. apply IHl; assumption.
Qed.

Theorem any_in_eq_dec_iff : forall (A: Type) `{EqDec A}, forall (l: list A) (x: A),
  (In x l <-> any (eqf x) l = true).
Proof.
  intros A eq_dec l x. apply reflect_iff. apply any_in_eq_dec.
Qed.

Lemma in_any_true : forall (A: Type) (l: list A) (x: A) (p : A -> bool), 
  p x = true -> In x l -> any p l = true.
Proof.
  intros A l x p H I. induction l.
  - cbn in I. auto.
  - cbn in *. destruct I. 
    + subst. rewrite H. reflexivity.
    + destruct (p a) eqn:H1.
      * reflexivity.
      * apply IHl. assumption.
Qed.

Lemma exist_in_any : forall (A: Type) (l: list A) (p : A -> bool), 
  any p l = true -> exists x: A, p x = true /\ In x l.
Proof.
  intros A l p H. induction l.
  - cbn in H. inversion H.
  - cbn in *. destruct (p a) eqn:H0.
    + exists a. split; try assumption. left. reflexivity.
    + assert (exists x : A, p x = true /\ In x l) by (apply IHl; apply H).
      destruct H1. exists x. destruct H1. split; try assumption. right. assumption.
Qed. 

Lemma forall_in_any : forall (A: Type) (l: list A) (p : A -> bool), 
  any p l = false -> forall x: A, In x l -> p x = false.
Proof.
  intros A l. induction l.
  - cbn in *. intros _ _ x [].
  - intros p H x I. cbn in *. destruct (p a) eqn:H0.
    + inversion H.
    + destruct I.
      * subst. assumption.
      * apply IHl; assumption.
Qed. 

Theorem elem_eq_for_eq_dec : forall (A: Type), EqDec A -> forall x y: list A, 
  (Elem_eq x y <-> Same_elements x y).
Proof.
  unfold Elem_eq, Same_elements. intros A eq_dec l l'. split.
  - intros H x. specialize (H (eqf x)). rewrite any_in_eq_dec_iff, any_in_eq_dec_iff, H. 
    split; intro H0; apply H0.
  - intros H p. destruct (any p l) eqn:e1; destruct (any p l') eqn:e2; trivial.
    + assert (exists x: A, p x = true /\ In x l) by (apply exist_in_any; assumption).
      assert (forall x: A, In x l' -> p x = false) by (apply forall_in_any; assumption).
      destruct H0. rewrite H in H0. destruct H0. rewrite <- H0. apply H1. assumption. 
    + assert (exists x: A, p x = true /\ In x l') by (apply exist_in_any; assumption).
      assert (forall x: A, In x l -> p x = false) by (apply forall_in_any; assumption).
      destruct H0. rewrite <- H in H0. destruct H0. rewrite <- H0. symmetry. apply H1. assumption.
Qed. 

Inductive tree (A: Type) : Type :=
| leaf : tree A
| node : A -> tree A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A} _ _ _.

Class LinearOrder {A: Type} := {
  ord      : A -> A -> bool;
  refl     : forall x: A, ord x x = true;
  anti_sym : forall x y: A, ord x y = true -> ord y x = true -> x = y;
  trans    : forall x y z: A, ord x y = true -> ord y z = true -> ord x z = true;
  full     : forall x y, ord x y = true \/ ord y x = true;
}.

Definition comp {A: Type} `{LinearOrder A} (x y: A) := 
  if ord x y then (if ord y x then Eq else Gt) else Lt.

Definition treeComp {A: Type} `{LinearOrder A} (x: A) (t: tree A) :=
match t with
| leaf => None
| node y _ _ =>  Some (comp x y)
end.

Fixpoint add_tree {A: Type} `{LinearOrder A} (x: A) (t : tree A) : tree A :=
match t with
| leaf => node x leaf leaf
| node v l r => match comp x v with
                | Lt => node v (add_tree x l) r
                | Eq => node v l r
                | Gt => node v l (add_tree x r)
                end
end.

Fixpoint to_tree {A: Type} `{LinearOrder A} (l : list A) : tree A := 
  match l with
  | []      => leaf
  | (x::l') => add_tree x (to_tree l')
  end.

Fixpoint to_list {A: Type} (l : tree A) : list A := 
  match l with
  | leaf       => []
  | node x l r => to_list l ++ [x] ++ to_list r
  end.

Fixpoint TCount {A: Type}(p: A -> bool)(t: tree A) : nat :=
  match t with
  | leaf => 0
  | node x l r => if (p x) then S (TCount p l + TCount p r) else TCount p l + TCount p r
  end.

Fixpoint TAny {A: Type}(p: A -> bool)(t: tree A) : bool :=
  match t with
  | leaf => false
  | node x l r => p x || TAny p l || TAny p r
  end.

Fixpoint count {A: Type} (p: A -> bool) (l: list A): nat :=
  match l with
  | nil => O
  | cons h t => if p h then S (count p t) else count p t
  end.

Definition permutation {A: Type} (a b : list A) :=
  forall p : A -> bool, count p a = count p b.

Definition TListPermutation{A: Type}(t: tree A)(l: list A) : Prop :=
  forall p: A->bool, TCount p t = count p l.

Definition TPermutation{A: Type}(t1 t2: tree A) : Prop :=
  forall p: A->bool, TCount p t1 = TCount p t2.

Definition TElem_eq (A: Type) (l l' : tree A) : Prop := 
  forall p : A -> bool, TAny p l = TAny p l'.

Definition TListElem_eq {A: Type} (t: tree A) (l: list A) : Prop :=
  forall p : A -> bool, TAny p t = any p l.

Definition DSort {A: Type} `{LinearOrder A} (l : list A) : list A := to_list (to_tree l).

Lemma count_list_concat {A: Type} (l l': list A): 
  forall p: A-> bool, count p (l ++ l') = count p l + count p l'.
Proof.
  intros p. revert l'. induction l; intros l'.
  - cbn. reflexivity.
  - cbn. destruct (p a).
    + rewrite IHl. cbn. reflexivity.
    + apply IHl.
Qed.
 
Lemma to_list_perm {A: Type} (t: tree A) : TListPermutation t (to_list t).
Proof.
  intros p. induction t.
  - cbn. reflexivity.
  - cbn. rewrite count_list_concat. cbn. destruct (p a).
    + rewrite plus_n_Sm, IHt1, IHt2. reflexivity.
    + rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma count_TCount {A: Type} (t: tree A) : forall p: A-> bool,
  TCount p t = count p (to_list t).
Proof.
  apply to_list_perm.
Qed.

Fixpoint TIn {A: Type} (x: A) (t: tree A) : Prop :=
match t with 
| leaf => False
| node v l r => v = x \/ TIn x l \/ TIn x r
end.

Inductive normal_tree {A: Type} `{LinearOrder A} : tree A -> Prop :=
| NormLeaf : normal_tree leaf
| NormNode : forall (x: A) (l r: tree A), normal_tree l -> normal_tree r ->
  (forall y: A, TIn y l -> comp y x = Lt) -> (forall y: A, TIn y r -> comp y x = Gt) ->
  normal_tree (node x l r).

Definition TDeduplicated {A: Type} `{EqDec A} (t: tree A) : Prop := 
  forall x : A, TIn x t -> TCount (eqf x) t = 1.

Definition LDeduplicated {A: Type} `{EqDec A} (t: list A) : Prop := 
  forall x : A, In x t -> count (eqf x) t = 1.

Global Instance lo_eq_dec {A: Type} `{LinearOrder A} : EqDec A.
Proof.
  exists (fun x y => if ord x y then (if ord y x then true else false) else false).
  intros x y. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2.
  - constructor. apply  anti_sym; assumption.
  - constructor. intro H0. subst. rewrite e2 in e1. inversion e1. 
  - constructor. intro H0. subst. rewrite e1 in e2. inversion e2.
  - constructor. intro H0. subst. assert (ord y y = true) by apply refl. rewrite e1 in H0. inversion H0.
Qed.

Lemma in_to_list {A: Type} (x: A) (t: tree A) : In x (to_list t) <-> TIn x t.
Proof.
  split.
  - induction t.
    + cbn. auto.
    + cbn. intro H. rewrite in_app_iff in H. cbn in *. destruct H; try destruct H.
      * right. left. apply IHt1. assumption.
      * left. assumption.
      * right. right. apply IHt2. assumption.
  - induction t.
    + cbn. auto.
    + cbn. intro H. rewrite in_app_iff. cbn. destruct H; cycle 1. destruct H.
      * left. apply IHt1. assumption.
      * right. right. apply IHt2. assumption.
      * right. left. assumption.
Qed.

Lemma not_full {A: Type} `{LinearOrder A} (x y: A) : ~ (ord x y = false /\ ord y x = false).
Proof.
  intros (a & b). destruct (full x y).
  - rewrite H0 in a. discriminate.
  - rewrite H0 in b. discriminate.
Qed.

Lemma comp_eq {A: Type} `{LinearOrder A} (x y: A) : comp x y = Eq <-> x = y.
Proof.
  split.
  - unfold comp. intro C. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2; try inversion C.
  apply anti_sym; assumption.
  - intros []. unfold comp. rewrite refl. auto.
Qed.

Lemma comp_lt {A: Type} `{LinearOrder A} (x y: A) : 
  comp x y = Lt <-> ord x y = false /\ ord y x = true.
Proof.
  unfold comp. split.
  - intro C. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2; try inversion C; auto.
    exfalso. apply (not_full x y); split; assumption.
  - intros (e1 & e2). rewrite e1. auto.
Qed.

Lemma comp_gt {A: Type} `{LinearOrder A} (x y: A) : 
  comp x y = Gt <-> ord x y = true /\ ord y x = false.
Proof.
  unfold comp. split.
  - intro C. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2; try inversion C; auto.
  - intros (e1 & e2). rewrite e1. rewrite e2. auto.
Qed.

Lemma ord_false_true {A: Type} `{LinearOrder A} (x y z: A) : 
  ord x y = false -> ord y x = true.
Proof.
  intros. destruct (full x y).
  - rewrite H0 in H1. discriminate.
  - assumption.
Qed.

Lemma lo_false_trans {A: Type} `{LinearOrder A} (x y z: A) : 
  ord y x = false -> ord z y = false -> ord z x = false.
Proof. 
  intros H1 H2.
  destruct (ord x z) eqn:H3.
  - assert (x <> z).
    + intro. subst. exfalso. apply (not_full y z); split; assumption.
    + destruct (ord z x) eqn:H4.
      * destruct (anti_sym x z H3 H4). exfalso. apply H0. auto.
      * reflexivity.
  - assert (ord x z = true).
    + apply (trans x y z); apply ord_false_true; assumption.
    + rewrite H0 in H3. discriminate.
Qed.

Lemma comp_trans {A: Type} `{LinearOrder A} (x y z: A) (c: comparison) :
  comp x y = c -> comp y z = c -> comp x z = c.
Proof.
  destruct c.
  - rewrite (comp_eq x y), (comp_eq y z), (comp_eq x z). intros. subst. auto.
  - rewrite (comp_lt x y), (comp_lt y z), (comp_lt x z). 
    intros (f1 & t1) (f2 & t2). split.
    + apply (lo_false_trans z y x); assumption.
    + apply (trans z y x); assumption.
  - rewrite (comp_gt x y), (comp_gt y z), (comp_gt x z).
    intros (t1 & f1) (t2 & f2). split.
    + apply (trans x y z); assumption.
    + apply (lo_false_trans x y z); assumption.
Qed.

Definition comp_inv (c: comparison) :=
match c with 
| Lt => Gt
| Eq => Eq
| Gt => Lt
end.

Lemma comp_inv_def {A: Type} `{LinearOrder A} (x y: A):
  comp y x = comp_inv (comp x y).
Proof.
  unfold comp. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2; cbn; auto.
  exfalso. apply (not_full x y); split; assumption.
Qed.

Lemma comp_inv_iff {A: Type} `{LinearOrder A} (x y: A) (c: comparison):
  comp y x = c <-> comp x y = comp_inv c.
Proof.
  rewrite comp_inv_def. split; intro O; destruct c; destruct (comp x y); cbn in *; auto; inversion O.
Qed.

Lemma add_dont_remove {A: Type} `{LinearOrder A} (t : tree A) : 
  forall v: A, TIn v t -> forall n: A, TIn v (add_tree n t).
Proof.
  intros v I n. induction t.
  - cbn in *. destruct I.
  - cbn in *. destruct (comp n a) eqn:c.
    + apply I.
    + cbn. destruct I as [e|[l | r]]; subst; auto.
    + cbn. destruct I as [e|[l | r]]; subst; auto.
Qed.

Lemma TIn_add {A: Type} `{LinearOrder A} (n: A) (t : tree A) : 
  forall v: A, TIn v (add_tree n t) <-> n = v \/ TIn v t.
Proof.
  intros v. split.
  - intros I. induction t.
    + left. cbn in *. destruct I; auto; try destruct H0; try destruct H0.
    + cbn in *. destruct (comp n a) eqn:c.
      * rewrite comp_eq in c. subst. cbn in *. destruct I as [e|[l|r]]; subst; auto.
      * cbn in *. destruct I as [e|[l|r]]; subst; auto. specialize (IHt1 l). destruct IHt1; auto.
      * cbn in *. destruct I as [e|[l|r]]; subst; auto. specialize (IHt2 r). destruct IHt2; auto.
  - intros [e | I].
    + induction t.
      * cbn. auto.
      * cbn. destruct (comp n a) eqn:c; cbn; auto. rewrite comp_eq in c. subst. auto.
    + apply add_dont_remove. assumption.
Qed.

Theorem add_preserves_normal {A: Type} `{LinearOrder A} (n: A) (t : tree A) : 
  normal_tree t -> normal_tree (add_tree n t).
Proof.
  intro N. induction N.
  - cbn. constructor; try constructor; intros y I; cbn in *; try inversion I.
  - cbn in *. destruct (comp n x) eqn:c.
    + constructor; assumption.
    + constructor; auto. intros y I. rewrite TIn_add in I. destruct I; subst; auto.
    + constructor; auto. intros y I. rewrite TIn_add in I. destruct I; subst; auto.
Qed.

Lemma TCount_for_not_satisfied_pred {A: Type} (t : tree A) (p: A -> bool): 
  (forall x:A, TIn x t -> p x = false) -> TCount p t = 0.
Proof.
  intros N. induction t.
  - auto.
  - cbn in *. rewrite (N a); auto. rewrite IHt1, IHt2; auto.
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

Theorem normal_is_depup {A: Type} `{LinearOrder A} (t: tree A) : 
  normal_tree t -> TDeduplicated t.
Proof.
  intro N. induction N.
  - intros x I. cbn in I. destruct I.
  - intros y I. cbn in I. destruct I as [e|[I|I]].
    + subst. cbn in *. rewrite eqf_refl. rewrite TCount_for_not_satisfied_pred, TCount_for_not_satisfied_pred; auto.
      * intros x I. rewrite <-eqf_comp_not_eq. specialize (H1 x I). rewrite comp_inv_iff. cbn. rewrite H1. intros [=].
      * intros x I. rewrite <-eqf_comp_not_eq. specialize (H0 x I). rewrite comp_inv_iff. cbn. rewrite H0. intros [=].
    + destruct (comp y x) eqn:c.
      * specialize (H0 y I). rewrite H0 in c. inversion c.
      * cbn. rewrite eqf_lt; auto. rewrite IHN1; auto. rewrite TCount_for_not_satisfied_pred; auto.
        intros z I'. rewrite <-eqf_comp_not_eq. rewrite comp_eq. specialize (H1 z I'). intros c'.
        subst. rewrite c in H1. discriminate.
      * cbn. rewrite eqf_lt; auto. rewrite IHN1; auto. rewrite TCount_for_not_satisfied_pred; auto.
        intros z I'. rewrite <-eqf_comp_not_eq. rewrite comp_eq. specialize (H1 z I'). specialize (H0 y I).
        intros e. subst. rewrite H1 in H0. discriminate.
    + destruct (comp y x) eqn:c.
      * specialize (H1 y I). rewrite H1 in c. inversion c.
      * cbn. rewrite eqf_lt; auto. rewrite IHN2; auto. rewrite TCount_for_not_satisfied_pred; auto.
        intros z I'. rewrite <-eqf_comp_not_eq. rewrite comp_eq. intro e; subst. specialize (H0 z I').
        specialize (H1 z I). rewrite H0 in H1. discriminate.
      * cbn. rewrite eqf_gt; auto. rewrite IHN2; auto. rewrite TCount_for_not_satisfied_pred; auto.
        intros z I'. rewrite <-eqf_comp_not_eq. rewrite comp_eq. intro e; subst. specialize (H0 z I'). 
        rewrite c in H0. discriminate.
Qed.

Theorem to_tree_normal {A: Type} `{LinearOrder A} (l: list A) : normal_tree (to_tree l).
Proof.
  induction l.
  - cbn in *. constructor.
  - cbn in *. apply add_preserves_normal. assumption.
Qed.

Theorem to_tree_dedup {A: Type} `{LinearOrder A} (l: list A) : TDeduplicated (to_tree l).
Proof.
  apply normal_is_depup. apply to_tree_normal.
Qed.

Theorem dedup_DSort {A: Type} `{LinearOrder A} (l : list A) : LDeduplicated (DSort l).
Proof.
  intros x I. unfold DSort in *. rewrite <- count_TCount. rewrite in_to_list in I.
  apply to_tree_dedup. assumption.
Qed.






(* Sorted *)

Inductive Sorted {A: Type} `{LinearOrder A} : list A -> Prop :=
  | SortedNil : Sorted []
  | SortedSing : forall h: A, Sorted [h]
  | SortedCons : forall h h' : A, forall t: list A,
      Sorted (h' :: t) -> ord h' h = true -> Sorted (h :: h' :: t).

Lemma sorted_without_head {A: Type} `{LinearOrder A} (a: A) (l: list A) :
  Sorted (a::l) -> Sorted l.
Proof.
  induction l; intro h.
  - constructor.
  - dependent destruction h. assumption.
Qed. 

Lemma concat_sorted {A: Type} `{LinearOrder A} (h: A) (l l': list A) : Sorted l -> Sorted (h::l') -> 
  (forall x: A, In x l -> ord h x = true) -> Sorted (l ++ (h::l')).
Proof.
  intros s1 s2 N. induction l.
  - cbn. assumption.
  - destruct l.
    + cbn. constructor; auto. apply (N a). cbn. auto.
    + cbn in *. constructor.
      * apply IHl.
        -- apply (sorted_without_head a). assumption.
        -- intros x I. apply N. auto.
      * dependent destruction s1. assumption.
Qed. 

Lemma head_sorted {A: Type} `{LinearOrder A} (h: A) (l: list A) : Sorted l -> 
  (forall x: A, In x l -> ord x h = true) -> Sorted (h::l).
Proof.
  intros s N. induction l.
  - constructor.
  - constructor; auto. apply N. cbn. auto.
Qed. 

Lemma ord_comp_lt {A: Type} `{LinearOrder A} (h: A) (l: list A) : 
  (forall x: A, In x l -> comp x h = Lt) -> (forall x: A, In x l -> ord h x = true).
Proof.
  unfold comp. intros R x I. specialize (R x I). destruct (ord h x) eqn:e1; destruct (ord x h) eqn:e2; auto.
  - inversion R.
  - destruct (full h x).
    + rewrite H0 in e1. discriminate.
    + rewrite H0 in e2. discriminate.
Qed.

Lemma ord_comp_gt {A: Type} `{LinearOrder A} (h: A) (l: list A) : 
  (forall x: A, In x l -> comp x h = Gt) -> (forall x: A, In x l -> ord x h = true).
Proof.
  unfold comp. intros R x I. specialize (R x I). destruct (ord h x) eqn:e1; destruct (ord x h) eqn:e2; auto.
  - inversion R.
  - destruct (full h x).
    + rewrite H0 in e1. discriminate.
    + rewrite H0 in e2. discriminate.
Qed.

Theorem normal_to_list_sorted {A: Type} `{LinearOrder A} (t: tree A) : normal_tree t -> Sorted (to_list t).
Proof.
  intros N. induction N.
  - cbn. constructor.
  - cbn. apply concat_sorted; auto.
    + apply head_sorted; auto. apply ord_comp_gt. intros z I. rewrite in_to_list in I. apply (H1 z I).
    + apply ord_comp_lt. intros z I. rewrite in_to_list in I. apply (H0 z I).
Qed.

Theorem sorted_DSort {A: Type} `{LinearOrder A} (l : list A) : Sorted (DSort l).
Proof.
  apply normal_to_list_sorted. apply to_tree_normal.
Qed.










(* Preserves elems *)

Lemma any_concat {A: Type} (l l': list A) (p: A -> bool): any p (l ++ l') = any p l || any p l'.
Proof.
  induction l; auto. cbn. destruct (p a); auto.
Qed.

Lemma to_list_any {A: Type} (t: tree A) : TListElem_eq t (to_list t).
Proof.
  intros p. induction t.
  - cbn. reflexivity.
  - cbn. rewrite any_concat. cbn. destruct (p a); cbn; auto.
    + rewrite orb_comm. auto.
    + rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma add_tree_any {A: Type} `{LinearOrder A} (x: A) (t: tree A) (p: A->bool):
  TAny p (add_tree x t) = (if p x then true else TAny p t).
Proof.
  induction t.
  - cbn. destruct (p x); auto.
  - cbn. destruct (comp x a) eqn:e; cbn.
    + rewrite comp_eq in e. subst. destruct (p a) eqn:p_a; auto.
    + rewrite IHt1. destruct (p a); destruct (p x); auto.
    + rewrite IHt2. destruct (p a); destruct (p x); auto. rewrite orb_false_l, orb_comm. auto.
Qed.

Lemma to_tree_any {A: Type} `{LinearOrder A} (l: list A) : TListElem_eq (to_tree l) l.
Proof.
  intros p. induction l.
  - cbn. reflexivity.
  - cbn. rewrite add_tree_any, IHl. auto.
Qed.

Theorem same_elements_DSort {A: Type} `{LinearOrder A} (l : list A) : Elem_eq l (DSort l).
Proof.
  unfold DSort. intros p. rewrite <-to_list_any. symmetry. apply to_tree_any.
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
  intros pred I. induction l.
  - cbn in *. inversion I.
  - cbn in *. destruct I.
    + subst. rewrite pred. apply neq_succ_0.
    + destruct (p a); auto.
Qed.

Theorem dup_def_eq {A: Type} `{LinearOrder A} (l : list A) : 
  Deduplicated l <-> LDeduplicated l.
Proof.
  unfold LDeduplicated. split.
  - intros D x I. induction D.
    + cbn in *. inversion I.
    + cbn in *. destruct I.
      * subst. rewrite eqf_refl. rewrite count_for_not_satisfied_pred; auto. intros y I.
        rewrite <- not_eqf_iff. intros e. subst. apply H0. assumption.
      * rewrite (IHD H1). assert (x <> x0) by (intro e; subst; auto). rewrite not_eqf_iff in H2.
        rewrite H2. auto.
  - intro D. induction l; constructor.
    + intro I. specialize (D a (or_intror I)). cbn in D. rewrite eqf_refl in D. assert (count (eqf a) l <> O).
      * apply count_existing with (x := a); auto. apply eqf_refl.
      * rewrite neq_0_r in H0. destruct H0 as (m & S). rewrite S in D. inversion D.
    + apply IHl. intros x I. cbn in *. specialize (D x (or_intror I)). destruct (eqf x a) eqn:e.
      * rewrite <- eqf_iff in e. subst. assert (count (eqf a) l <> O).
        -- apply count_existing with (x := a); auto. apply eqf_refl.
        -- rewrite neq_0_r in H0. destruct H0 as (m & S). rewrite S in D. inversion D. 
      * assumption.
Qed.

Theorem unique_sorted {A: Type} `{LinearOrder A} (l l': list A) : 
  permutation l l' -> Sorted l -> Sorted l' -> l = l'.
Proof.
Admitted.

Fixpoint remove {A: Type} `{EqDec A} (x: A) (l: list A) :=
match l with 
| []     => []
| (h::t) => if eqf x h then t else h :: remove x t
end.

Lemma remove_count_true {A: Type} `{EqDec A} (h: A) (l: list A) (p: A -> bool) :
  In h l -> p h = true -> count p l = S (count p (remove h l)).
Proof.
  induction l; intros I t.
  - cbn in *. destruct I. 
  - cbn in *. destruct I.
    + subst. rewrite t. rewrite eqf_refl. auto.
    + destruct (p a) eqn:e; destruct (eqf h a) eqn:e1; auto.
      * cbn in *. rewrite e. rewrite IHl; auto.
      * rewrite <- eqf_iff in e1. subst. rewrite t in e. discriminate.
      * cbn in *. rewrite e. apply IHl; auto.
Qed.

Lemma remove_count_false {A: Type} `{EqDec A} (h: A) (l: list A) (p: A -> bool) :
  p h = false -> count p l = count p (remove h l).
Proof.
  induction l; intros f; auto. cbn in *. 
  destruct (p a) eqn:e; destruct (eqf h a) eqn:e1; auto.
  - rewrite <- eqf_iff in e1. subst. rewrite f in e. discriminate.
  - cbn. rewrite e. f_equal. apply IHl; auto.
  - cbn. rewrite e. apply IHl; auto.
Qed.

Lemma in_count_not_O {A: Type} `{EqDec A} (l: list A) (x: A) :
  In x l <-> count (eqf x) l <> O.
Proof.
  split.
  - intros I. induction l.
    + cbn in I. destruct I.
    + cbn in *. destruct I as [e|I].
      * subst. rewrite eqf_refl. auto.
      * destruct (eqf x a) eqn: e; auto.
  - intros C. induction l.
    + cbn in C. contradiction.
    + cbn in *. destruct (eqf x a) eqn: e; auto. rewrite <- eqf_iff in e.
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
  - assert (In h l'). 
    + apply (perm_in [h]); auto. cbn. auto. 
    + cbn. apply eq_add_S. specialize (perm p). cbn in *. destruct (p h) eqn:e.
      * rewrite <-remove_count_true; auto.
      * rewrite <-remove_count_false; auto.
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
  unfold permutation. revert l'. induction l; intros l' I perm p.
  - cbn in *. specialize (perm p). destruct (p h) eqn: e.
    + rewrite (remove_count_true h); auto.
    + rewrite (remove_count_false h); auto.
  - cbn in *. specialize (perm p). destruct (p h) eqn: e.
    + rewrite (remove_count_true h l'); auto.
    + rewrite (remove_count_false h l'); auto.
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



(* normal function *)

Definition normalzation {A: Type} (f: A -> A) :=
  forall x: A, f x = f (f x).

Theorem DSort_normal {A: Type} `{LinearOrder A} : normalzation DSort.
Proof.
  red. intros l. apply deduo_sort_uniquenss.
  - apply same_elements_DSort.
  - apply sorted_DSort.
  - apply sorted_DSort.
  - rewrite dup_def_eq. apply dedup_DSort. 
  - rewrite dup_def_eq. apply dedup_DSort. 
Qed.

Class equivalance_relation {A: Type} (R: A -> A -> Prop) := equiv_proof {
  equiv_refl  : forall x: A, R x x;
  equiv_sym   : forall x y: A, R x y -> R y x;
  equiv_trans : forall x y z: A, R x y -> R y z -> R x z;
}.

Theorem eq_elem_equiv {A: Type} : equivalance_relation (Elem_eq (A := A)).
Proof.
  apply equiv_proof.
  - intros x p. reflexivity.
  - intros x y eq p. rewrite eq. reflexivity.
  - intros x y z eq1 eq2 p. rewrite eq1, eq2. reflexivity.
Qed.


