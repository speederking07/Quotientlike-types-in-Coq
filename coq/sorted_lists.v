Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import Coq.Lists.List.
Import ListNotations.

Set Printing Projections.

Inductive Option (A: Type) :=
  | None : Option A
  | Some : A -> Option A.

Arguments None {A}.
Arguments Some {A}.

Inductive SList (A: Type) (ord : A -> A -> bool) : Option A -> Type :=
  | SNil : SList A ord None
  | SCons : forall hd: Option A, forall a : A, forall l : SList A ord hd,  
     (hd = None \/ (forall h: A, hd = Some h /\ord a h = true)) -> SList A ord (Some a).

Fixpoint toList {A: Type} {ord:  A -> A -> bool} {hd: Option A} (l: SList A ord hd) : list A :=
  match l with
  | SNil _ _ => nil
  | SCons _ _ _ hd tl _ => hd :: toList tl
  end.

Print SCons.

Inductive Sorted {A: Type} (ord : A -> A -> bool) : list A -> Prop :=
  | SortedNil : Sorted ord []
  | SortedSing : forall h: A, Sorted ord [h]
  | SortedCons : forall h h' : A, forall t: list A,
      Sorted ord (h' :: t) -> ord h h' = true -> Sorted ord (h :: h' :: t).

Lemma sorted_without_head : forall A: Type, forall ord:A -> A -> bool, forall l: list A, forall a: A,
  Sorted ord (a::l) -> Sorted ord l.
Proof.
  intros A ord l. induction l; intro h.
  - intros _. constructor.
  - intro s. dependent destruction s. assumption.
Qed.

Lemma sorted_with_head : forall A: Type, forall ord:A -> A -> bool, forall l: list A, forall a h: A,
  Sorted ord (h::l) -> ord a h = true -> Sorted ord (a::h::l).
Proof.
  intros A ord l a h sort o. constructor.
  - trivial.
  - assumption.
Qed. 

Record SortedList (A: Type) (ord: A -> A -> bool) := {
  val : list A;
  proof : Sorted ord val
}.

Arguments val {A} {ord} _.
Arguments proof {A} {ord} _.

Theorem none_is_empty : forall A: Type, forall ord:  A -> A -> bool, 
    forall l : SList A ord None, l = SNil A ord.
Proof.
  intros A ord l. dependent destruction l. trivial.
Qed.

Check or_introl.

Theorem isSorted : forall A: Type, forall ord:  A -> A -> bool, forall hd : Option A, 
    forall l : SList A ord hd, Sorted ord (toList l).
Proof.
  intros A ord hd list. induction list.
  - cbv. constructor.
  - destruct o.
    + subst. dependent destruction list. cbv. constructor.
    + destruct hd.
      * destruct (a0 a). inversion H.
      * destruct (a0 a1). dependent destruction list. apply (SortedCons ord a a1 (toList list)).
        -- trivial.
        -- trivial.
Qed.

Definition SList_to_SortedList {A: Type} {ord: A -> A -> bool} {hd: Option A} 
    (l: SList A ord hd) : SortedList A ord := {|
  val := toList l;
  proof := isSorted A ord hd l
|}.

Record LinearOrder {A: Type} (ord: A -> A -> bool) := {
  refl : forall x: A, ord x x = true;
  anti_sym : forall x y: A, ord x y = true -> ord y x = true -> x = y;
  trans : forall x y z: A, ord x y = true -> ord y z = true -> ord x z = true;
  full : forall x y, ord x y = true \/ ord y x = true;
}.

Theorem sorted_lo_head_relation : forall A: Type, forall ord: A->A->bool, LinearOrder ord -> 
  forall l: list A, forall h: A, Sorted ord (h::l) -> forall x: A, In x (h :: l) ->
  ord h x = true.
Proof.
  intros A ord lo l. induction l; intros h sort x H.
  - cbn in H. destruct H.
    + destruct lo. subst. apply refl0.
    + contradiction.
  - cbn in H. destruct H.
    + subst. destruct lo. apply refl0.
    + cut (ord a x = true).
      * intro H0. dependent destruction sort; try discriminate. destruct lo.
        apply (trans0 h a x); assumption.
      * apply IHl.
        -- apply (sorted_without_head A ord (a::l) h). assumption.
        -- assumption.
Qed.

Fixpoint count {A: Type} (p: A -> bool) (l: list A): nat :=
  match l with
  | nil => O
  | cons h t => if p h then S (count p t) else count p t
  end.

Definition permutation {A: Type} (a b : list A) :=
  forall p : A -> bool, count p a = count p b.

Theorem perm_sym : forall A: Type, forall l l': list A, permutation l l' <-> permutation l' l.
Proof.
  intros A l l'. unfold permutation. split; intros H p; symmetry; apply (H p).
Qed.

Theorem perm_trans : forall A: Type, forall x y z: list A, 
  permutation x y -> permutation y z -> permutation x z.
Proof.
  intros A x y z H H0. unfold permutation in *. intro p. specialize (H p). specialize (H0 p).
  transitivity (count p y); assumption.
Qed.

Lemma perm_without_head : forall A: Type, forall l l': list A, forall a: A,
  permutation (cons a l) (cons a l') -> permutation l l'.
Proof.
  - intros A l l' a H. unfold permutation in *. intro p. specialize (H p). cbn in H.
    destruct (p a).
    + inversion H. reflexivity. 
    + assumption.
Qed.

Lemma perm_with_head : forall A: Type, forall l l': list A, forall a: A,
  permutation l l' -> permutation (a::l) (a::l').
Proof.
  intros A l l' a perm. unfold permutation in *. intro p. specialize (perm p).
  cbn. destruct (p a).
  - destruct perm. trivial.
  - assumption.
Qed.

Theorem perm_for_element : forall A: Type, forall l l': list A, forall x: A,
  permutation l l' -> In x l' -> In x l.
Proof.
  unfold permutation. intros A l. induction l; intros l' x perm H.
  - destruct l'.
    + cbn in H. destruct H.
    + specialize (perm (fun x => true)). cbn in perm. discriminate.
  - destruct l'.
    + cbn in H. destruct H.
    + cbn. cbn in H. destruct H.
      * subst. left.
Abort.

Definition and (x y: bool) : bool :=
  if x then y else false.

Lemma eq_def_l0 : forall A: Type, forall ord: A -> A -> bool, forall x y: A,
   LinearOrder ord -> x = y <-> (forall p: A -> bool, p x = p y).
Proof.
  intros A ord x y. split.
  - intros e p. subst. reflexivity.
  - intro prop. destruct H. specialize (prop (fun z => and (ord z x) (ord x z))). cbn in prop.
    destruct (ord y x) eqn:b1; destruct (ord x y) eqn:b2.
    + apply anti_sym0; assumption.
    + specialize (refl0 x). rewrite refl0 in prop. cbn in prop. discriminate.
    + specialize (refl0 x). rewrite refl0 in prop. cbn in prop. discriminate.
    + specialize (refl0 x). rewrite refl0 in prop. cbn in prop. discriminate.
Qed.

Lemma singleton_perm : forall A: Type, forall ord: A -> A -> bool, forall x y: A,
   LinearOrder ord -> x = y <-> permutation [x] [y].
Proof.
  intros A ord x y lo. rewrite (eq_def_l0 A ord).
  - unfold permutation. cbn. split.
    + intros H p. specialize (H p). destruct H. trivial.
    + intros H p. specialize (H p). destruct (p x); destruct (p y); cbn in H;
      try discriminate; try trivial.
  - assumption.
Qed.

Definition eq_fun {A: Type} (f: A -> A -> bool) :=
  forall x y: A, f x y = true <-> x = y.

Theorem not_eq_fun : forall A: Type, forall f: A -> A -> bool, 
  eq_fun f -> forall x y: A, f x y = false <-> x <> y.
Proof.
  intros A f eq x y. split.
  - intros H p. subst. destruct (eq y y). assert (f y y = true) by auto.
    congruence.
  - intro. destruct (f x y) eqn:H1. 
    + destruct (eq x y). exfalso.
      apply H. apply H0. assumption.
    + reflexivity.
Qed.

Theorem eq_fun_sym : forall A: Type, forall f: A -> A -> bool, eq_fun f ->  forall x y: A, f x y = f y x.
Proof.
  intros A f q x y. cut (eq_fun f); [| assumption].
  intro e. unfold eq_fun in *. specialize (e x y). specialize (q y x). destruct (f x y).
  + symmetry. rewrite q. symmetry. rewrite <- e. trivial.
  + destruct (f y x); [| trivial].
    rewrite e. symmetry. rewrite <- q. trivial.
Qed.

Theorem eq_relf : forall A: Type, forall f: A -> A -> bool, eq_fun f -> forall x: A, f x x = true.
Proof.
  intros A f eq x. specialize (eq x x). rewrite eq. trivial.
Qed.
 
Definition ord_eq {A: Type} (ord: A -> A -> bool) := fun x y => and (ord x y) (ord y x).

Theorem ord_is_eq : forall A: Type, forall ord: A -> A -> bool, LinearOrder ord -> eq_fun (ord_eq ord).
Proof.
  intros A ord lo. unfold eq_fun. intros x y. unfold ord_eq. split.
  - intro. destruct (ord x y) eqn:e1; destruct (ord y x) eqn:e2; try discriminate.
    + destruct lo. apply anti_sym0; assumption.
  - intro. subst. destruct lo. specialize (refl0 y). rewrite -> refl0. cbn. trivial.
Qed.

Lemma week_eq_fun_in : forall A: Type, forall f: A->A->bool, 
  eq_fun f -> forall x: A, forall l: list A, In x l <-> count (f x) l <> O.
Proof.
  intros A f e x l. split.
  - intros H. induction l.
    + cbn in H. contradiction.
    + cbn. destruct (f x a) eqn:eq.
      * apply PeanoNat.Nat.neq_succ_0.
      * apply IHl. destruct H.
        -- subst. rewrite (eq_relf A) in eq.
           ++ discriminate.
           ++ assumption.
        -- assumption.
  - intro H. induction l.
    + cbn in H. contradiction.
    + cbn. destruct (f x a) eqn:eq.
      * left. destruct (e x a). symmetry. apply H0. assumption.
      * right. apply IHl. cbn in H. rewrite eq in H. assumption.
Qed.

Theorem weak_perm_for_element : forall A: Type, forall f: A->A->bool, forall l l': list A, forall x: A,  
  eq_fun f -> permutation l l' -> In x l' -> In x l.
Proof.
  unfold permutation. intros A f l l' x eq_f perm H. specialize (perm (f x)). cut (count (f x) l' <> O).
  - intro H0. rewrite <- perm in H0. rewrite (week_eq_fun_in A f eq_f). assumption.
  - rewrite <- (week_eq_fun_in A f eq_f). assumption.
Qed.

Lemma head_eq : forall A: Type, forall ord: A -> A -> bool, forall l l': list A, forall a a': A, 
  LinearOrder ord -> permutation (a :: l) (a' :: l') -> Sorted ord (a :: l) ->
  Sorted ord (a' :: l') -> a = a'.
Proof.
  intros A ord l l' h h' lo perm s1 s2. cut (eq_fun (ord_eq ord)); cycle 1.
  - apply ord_is_eq. assumption.
  - intro eq_fun. destruct (ord_eq ord h h') eqn:eq.
    + rewrite <- (eq_fun h h'). assumption.
    + assert (LinearOrder ord); try assumption. destruct H. destruct (full0 h h').
      * unfold ord_eq in eq. rewrite H in eq. cbn in eq. cut (In h (h'::l')).
        -- intro h_in. assert (ord h' h = true).
           ++ apply (sorted_lo_head_relation A ord lo l' h'); assumption.
           ++ rewrite H0 in eq. discriminate.
        -- apply (weak_perm_for_element A (ord_eq ord) (h'::l') (h :: l)  h).
           ++ assumption.
           ++ rewrite perm_sym. assumption.
           ++ cbn. left. reflexivity.
      * unfold ord_eq in eq. rewrite H in eq. cbv in eq. cut (In h' (h::l)).
        -- intro h_in. assert (ord h h' = true).
           ++ apply (sorted_lo_head_relation A ord lo l h); assumption.
           ++ rewrite H0 in eq. discriminate.
        -- apply (weak_perm_for_element A (ord_eq ord) (h :: l) (h'::l') h').
           ++ assumption.
           ++ assumption.
           ++ cbn. left. reflexivity.
Qed.

(* Unique *)

Theorem unique_representation: forall A: Type, forall ord:A -> A -> bool, LinearOrder ord -> 
  forall l l': list A, permutation l l' -> Sorted ord l -> Sorted ord l' -> l = l'.
Proof.
  intros A ord lo l. induction l; intros l' perm sort sort'.
  - destruct l'.
    + reflexivity.
    + specialize (perm (fun x => true)). cbn in perm. discriminate.
  - destruct l'.
    + specialize (perm (fun x => true)). cbn in perm. discriminate.
    + cut (a = a0).
      * intro H. subst. cut (l = l').
        -- intro H1. destruct H1. reflexivity.
        -- apply IHl.
           ++ apply (perm_without_head A l l' a0). assumption.
           ++ apply (sorted_without_head A ord l a0). assumption.
           ++ apply (sorted_without_head A ord l' a0). assumption.
      * apply (head_eq A ord l l' a a0); assumption.
Qed.

(* Sort *)

Inductive BT(A : Type) : Type :=
  | leaf : A -> (BT A)
  | node : (BT A)->(BT A)->(BT A).

Arguments leaf {A}.
Arguments node {A}.

Fixpoint BTInsert{A : Type}(x : A)(tree : BT A) :=
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

Fixpoint merge{A : Type}(ord : A -> A -> bool)(l1 : list A): (list A) -> list A :=
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

Fixpoint BTSort {A : Type}(ord : A -> A -> bool)(t : BT A): list A :=
  match t with
  | leaf x => [x]
  | node l r => merge ord (BTSort ord l) (BTSort ord r)
  end. 

Definition mergeSort{A: Type}(ord : A -> A -> bool)(l: list A): list A :=
  match l with
  | [] => []
  | x::l' => BTSort ord (listToBT x l')
  end.

Fixpoint BTToList{A: Type}(t: BT A) : list A :=
  match t with
  | leaf a => [a]
  | node l r => (BTToList l) ++ (BTToList r)
  end.

Require Import PeanoNat.
Import Nat.

(* Perm def *)
Fixpoint BTCount {A: Type}(p: A -> bool)(t: BT A) : nat :=
  match t with
  | leaf x => if p x then 1 else 0
  | node l r => BTCount p l + BTCount p r
  end.

Definition BTListPermutation{A: Type}(t: BT A)(l: list A) : Prop :=
  forall p: A->bool, BTCount p t = count p l.

Definition BTPermutation{A: Type}(t1 t2: BT A) : Prop :=
  forall p: A->bool, BTCount p t1 = BTCount p t2.

Theorem merge_perm : forall A: Type, forall p: A->bool, forall ord: A->A->bool, forall l1 l2 : list A,
  count p l1 + count p l2 = count p (merge ord l1 l2).
Proof.
  intros A p ord l1. induction l1; intros l2.
  - cbn. trivial.
  - intros. induction l2.
    + cbn. rewrite add_0_r. trivial.
    + cbn. case_eq (ord a a0); case_eq (ord a0 a); intros.
      * cbn. destruct (p a). cbn. f_equal. rewrite <- IHl1. cbn. trivial. rewrite <- IHl1. cbn. trivial.
      * cbn. destruct (p a). cbn. f_equal. rewrite <- IHl1. cbn. trivial. rewrite <- IHl1. cbn. trivial.
      * cbn in *. destruct (p a0).
        -- rewrite Nat.add_succ_r. f_equal. rewrite <- IHl2. trivial.
        -- rewrite <- IHl2. trivial.
      * cbn in *. destruct (p a0).
        -- rewrite Nat.add_succ_r. f_equal. rewrite <- IHl2. trivial.
        -- rewrite <- IHl2. trivial. 
Qed.

Theorem BTSort_is_perm : forall A:Type, forall ord: A->A->bool, forall t : BT A,
  forall p: A->bool, BTCount p t = count p (BTSort ord t).
Proof.
  intros A ord t. induction t; intro p.
  - cbn. constructor.
  - cbn. rewrite IHt1. rewrite IHt2. rewrite <- merge_perm. trivial.
Qed.

Theorem BT_insert_count : forall A : Type, forall p: A->bool, forall x : A, forall t : BT A,
  BTCount p (BTInsert x t) = if p x then  1+BTCount p t else BTCount p t.
Proof.
  intros A p x t. induction t.
  - intros. cbn. case_eq (p x); case_eq (p a); intros; cbn; trivial.
  - intros. cbn. rewrite IHt1. case_eq (p x); intros.
    + cbn. rewrite add_succ_r. rewrite add_comm. trivial.
    + rewrite add_comm. trivial. 
Qed.

Theorem BTSort_perm : forall A: Type, forall ord: A->A->bool, forall l : list A, forall x: A,
   permutation (x::l) (BTSort ord (listToBT x l)).
Proof.
  intros A ord l. induction l; intro x.
  - cbn. constructor.
  - cbn. unfold permutation. intros. rewrite <- BTSort_is_perm. cbn.
    rewrite BT_insert_count. case_eq (p x); intro.
    + cbn. f_equal. unfold permutation in *. cbn in *. rewrite IHl.
      rewrite <- BTSort_is_perm. trivial.
    + unfold permutation in *. cbn in *. rewrite IHl. rewrite <- BTSort_is_perm.
      trivial.
Qed.

Lemma ord_false_true : forall A: Type, forall f: A->A->bool, forall y x: A,
  LinearOrder f -> f x y = false -> f y x = true.
Proof.
  intros. destruct H. specialize (full0 x y). destruct full0.
  - rewrite H in H0. discriminate.
  - assumption.
Qed.

Lemma lo_false_trans : forall A: Type, forall f: A->A->bool, forall z y x: A,
  LinearOrder f -> f y x = false -> f z y = false -> f z x = false.
Proof. 
  intros A f z y x lo H H0. assert (LinearOrder f). trivial. destruct H1.
  destruct (f x z) eqn:H1.
  - assert (x <> z).
    + intro. subst. destruct (full0 y z).
      * rewrite H in H2. discriminate.
      * rewrite H0 in H2. discriminate.
    + destruct (f z x) eqn:H3.
      * specialize (H2 (anti_sym0 x z H1 H3)). destruct H2.
      * reflexivity.
  - assert (f x z = true).
    + apply (trans0 x y z); apply ord_false_true; assumption.
    + rewrite H1 in H2. discriminate.
Qed.

Theorem merged_sorted_lists : forall A: Type, forall ord: A->A->bool, LinearOrder ord -> 
  forall l1 l2: list A, Sorted ord l1 -> Sorted ord l2 -> Sorted ord (merge ord l1 l2).
Proof.
  intros A ord lo l1 l2 s1. revert l2. induction s1.
  - intros l2 s2. cbn. assumption.
  - intros l2 s2. induction s2.
    + cbn. constructor.
    + cbn. destruct (ord h h0) eqn:o.
      * constructor; try constructor; try assumption.
      * constructor.
        -- constructor.
        -- apply ord_false_true; assumption.
    + cbn. destruct (ord h h0) eqn:o.
      * destruct lo. assert (ord h h' = true).
        -- apply (trans0 h h0 h'); assumption.
        -- cbn in IHs2. rewrite H0 in IHs2. constructor. constructor.  
           ++ dependent destruction IHs2. assumption.
           ++ assumption.
           ++ assumption.
      * destruct (ord h h') eqn:o2.
        -- cbn in IHs2. rewrite o2 in IHs2. apply sorted_with_head. 
           ++ assumption.
           ++ apply ord_false_true; assumption.
        -- cbn in IHs2. rewrite o2 in IHs2. constructor; assumption.
  - intros l2 s2. induction s2.
    + specialize (IHs1 []). cbn in *. constructor.
      * apply IHs1. constructor.
      * assumption.
    + specialize (IHs1 [h0]). cbn. destruct (ord h' h0) eqn:o1.
      * assert (ord h h0 = true).
        -- destruct lo. apply (trans0 h h' h0); assumption.
        -- rewrite H0. constructor. 
           ++ cbn in IHs1. rewrite o1 in IHs1. apply IHs1. constructor.
           ++ assumption.
      * destruct (ord h h0) eqn:o2.
        -- cbn in IHs1. rewrite o1 in IHs1. constructor.
           ++ apply IHs1. constructor.
           ++ assumption.
        -- cbn in IHs1. rewrite o1 in IHs1. constructor. constructor.
           ++ apply (sorted_without_head A ord (h' :: t0) h0). apply IHs1. constructor.
           ++ assumption.
           ++ apply ord_false_true; assumption.
    + destruct (ord h h0) eqn:o1.
      * specialize (IHs1 (h0::h'0::t1)). cbn. rewrite o1. destruct (ord h' h0) eqn:o2.
        -- cbn in IHs1. rewrite o2 in IHs1. constructor.
           ++ apply IHs1. constructor; assumption.
           ++ assumption.
        -- cbn in IHs1. rewrite o2 in IHs1. constructor.
           ++ apply IHs1. constructor; assumption.
           ++ assumption.
      * cbn. rewrite o1. destruct (ord h h'0) eqn:o2.
        -- cbn in IHs2. rewrite o2 in IHs2. constructor.
           ++ apply IHs2.
           ++ apply ord_false_true; assumption.
        -- cbn in IHs2. rewrite o2 in IHs2. constructor.
           ++ apply IHs2.
           ++ assumption.
Qed.

Theorem BT_sorts: forall A: Type, forall ord: A->A->bool, LinearOrder ord -> 
  forall t: BT A, Sorted ord (BTSort ord t).
Proof.
  intros A ord lo t. induction t.
  - cbn. constructor.
  - cbn. apply merged_sorted_lists; assumption.
Qed.

Theorem sorted_list_is_sorted : forall A: Type, forall ord: A->A->bool, LinearOrder ord -> 
  forall l: list A, Sorted ord (mergeSort ord l) /\ permutation l (mergeSort ord l).
Proof.
  intros A ord lo l. split.  
  - induction l.
    + cbn. constructor.
    + cbn. apply BT_sorts. assumption.
  - induction l.
    + cbn. unfold permutation. intro. cbn. reflexivity.
    + cbn. apply BTSort_perm.
Qed.

Theorem merge_sort_idempotent : forall A: Type, forall ord: A->A->bool, LinearOrder ord -> 
  forall l: list A, (mergeSort ord l) = (mergeSort ord (mergeSort ord l)).
Proof.
  intros A ord lo l. apply (unique_representation A ord lo); 
  apply sorted_list_is_sorted; assumption.
Qed.

Require Import StrictProp.
Print StrictProp.

Fixpoint isSortedFix {A: Type} (ord: A->A->bool) (l: list A) : bool :=
  match l with 
  | [] => true
  | x :: l' => match l' with
               | [] => true
               | y :: l'' => if ord x y then isSortedFix ord l' else false
               end
  end.

Theorem isSortedFix_is_ok : forall A: Type, forall ord: A->A->bool, LinearOrder ord ->
  forall l: list A, isSortedFix ord l = true <-> Sorted ord l.
Proof.
  intros A ord lo. split.
  - intro H. induction l.
    + constructor.
    + destruct l.
      * constructor.
      * destruct (ord a a0) eqn:o; constructor.
        -- apply IHl. cbn. cbn in H. rewrite o in H. assumption.
        -- assumption.
        -- cbn in H. rewrite o in H. discriminate.
        -- cbn in H. rewrite o in H. discriminate.
  - intro H. induction H.
    + cbn. reflexivity.
    + cbn. reflexivity.
    + cbn. rewrite H0. assumption.
Qed.

Definition sSorted {A: Type} {ord: A->A->bool} (lo: LinearOrder ord) (l: list A) : SProp :=
 Squash (isSortedFix ord l = true).

Theorem merge_sort_sorts: forall A: Type, forall ord: A->A->bool, forall lo: LinearOrder ord,
  forall l: list A, sSorted lo (mergeSort ord l).
Proof.
  intros A ord lo l. constructor. rewrite isSortedFix_is_ok.
  - apply sorted_list_is_sorted. assumption.
  - assumption.
Qed.

Record MSet (A: Type) (ord: A -> A -> bool) (lo: LinearOrder ord) := {
  entries : list A;
  sorted : sSorted lo entries
}.

Arguments entries {A ord lo}.
Arguments sorted {A ord lo}.

Definition createMSet (A: Type) {ord: A -> A -> bool} (lo: LinearOrder ord) (val: list A) := {|
  entries := mergeSort ord val;
  sorted := (merge_sort_sorts A ord lo val)
|}.

Lemma sFalse : forall x: Prop, Squash (false = true) -> x.
  intros. apply sEmpty_ind. apply (Squash_sind (false = true)).
  - intros. discriminate.
  - assumption.
Qed.

Theorem MSet_eq : forall A: Type, forall ord: A->A->bool, forall lo: LinearOrder ord,
  forall l l': MSet A ord lo, permutation (entries l) (entries l') -> l = l'.
Proof.
  intros A ord lo l l' perm. destruct l. destruct l'. cbn in *. assert (entries0 = entries1).
  - unfold sSorted in *. apply (unique_representation A ord lo). 
    + assumption.
    + destruct (isSortedFix ord entries0) eqn:s.
      * rewrite <- isSortedFix_is_ok; assumption.
      * apply sFalse. assumption.
    + destruct (isSortedFix ord entries1) eqn:s.
      * rewrite <- isSortedFix_is_ok; assumption.
      * apply sFalse. assumption.
  - subst. reflexivity.
Qed.



