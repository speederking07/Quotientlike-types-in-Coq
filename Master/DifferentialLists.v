Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Bool.
Require Import Coq.Program.Equality.
Import PeanoNat.Nat.
Require Import Lia.
Import ListNotations.

Require Import Lib.Sorted.
Require Import Lib.EqDec.
Require Import Lib.LinearOrder.
Require Import Lib.MergeSort.

Class Diff (A: Type) `{E: EqDec A} := {
  D: Type;
  diff: A -> A -> D;
  add: A -> D -> A;

  diff_comm: forall x y, diff x y = diff y x;
  diff_def: forall x d, d = diff x (add x d);
  recover: forall x y, y = add x (diff x y) \/ x = add y (diff x y);
  diff_anti_sym : forall x d, x = add (add x d) d -> d = diff x x;
  diff_trans: forall x y z, 
    z = add (add x (diff x y)) (diff y z) -> z = add x (diff x z);
}.

Lemma diff_anty_sym' (A: Type) `{Diff A} :
  forall x y, y = add x (diff x y) -> x = add y (diff x y) -> x = y.
Proof.
  intros x y P Q. assert (diff x y = diff x x). {
    apply (diff_anti_sym x). rewrite <- P, <- Q. auto.
  } rewrite P, H0. destruct (recover x x); auto.
Qed.


Theorem diff_uniq(A: Type) `{Diff A}: forall x d d', add x d = add x d' -> d = d'.
Proof.
  intros x d d' Heq. rewrite (diff_def x), <- Heq, <- diff_def; auto.
Qed.

Global Instance Diff_is_LO (A: Type) `{D: Diff A} : LinearOrder A.
Proof.
  exists (fun x y => eqf y (add x (diff y x))).
  - intros x. destruct (eqf_leibniz x (add x (diff x x))); auto. 
    destruct (recover x x); rewrite <- H in n; contradiction.
  - intros x y. rewrite (diff_comm y), <- eqf_iff, <- eqf_iff. intros e e'. 
    apply (diff_anty_sym' A x y); auto.
  - intros x y z e e'. rewrite <- eqf_iff, diff_comm in *. apply (diff_trans x y z). 
    remember (diff x y) as d. remember (diff y z) as d'. rewrite e', e. auto.
  - intros x y. rewrite <- eqf_iff, <- eqf_iff in *. destruct (recover x y); auto.
    rewrite (diff_comm y). auto.
Defined.



Definition DiffList (A: Type) `{Diff A} :=
  option (A * list D).

Fixpoint from_diff' {A: Type} `{Diff A} (x: A) (l: list D) :=
  match l with
  | []        => [x]
  | (h :: l') => x :: from_diff' (add x h) l'
  end.

Definition from_diff {A: Type} `{Diff A} (x: DiffList A) : list A :=
  match x with
  | None        => []
  | Some (a, l) => (from_diff' a l)
  end.

Fixpoint to_diff_sorted' {A: Type} `{Diff A} (p: A) (l: list A) : list D :=
  match l with
  | [] => []
  | (h :: t) => diff p h :: to_diff_sorted' h t
  end.

Definition to_diff_sorted {A: Type} `{Diff A} (l: list A) : DiffList A :=
  match l with
  | [] => None
  | (h :: t) => Some (h, to_diff_sorted' h t)
  end.

Definition to_diff {A: Type} `{Diff A} (l: list A) : DiffList A :=
  to_diff_sorted (mergeSort ord l).

Theorem diff'_epi {A: Type} `{Diff A} (l: list D) (x h: A) :
  to_diff_sorted' x (from_diff' h l) = (diff x h :: l).
Proof.
  revert x h. induction l; auto. intros x h. cbn. f_equal. 
  assert (a :: l = diff h (add h a) :: l) by (rewrite <- diff_def; auto). rewrite H0.
  apply IHl.
Qed.

Theorem diff_epi {A: Type} `{Diff A} (l: DiffList A) :
  to_diff_sorted (from_diff l) = l.
Proof.
  destruct l as [(a & l)|]; cbn; auto.
  revert a. induction l; cbn; intro h; auto.
  f_equal; f_equal. rewrite diff'_epi, <- diff_def. auto.
Qed.

Theorem diff_mono {A: Type} `{Diff A} (l: list A) :
  Sorted l -> from_diff (to_diff_sorted l) = l.
Proof.
  intros s. induction s; auto. cbn in *. f_equal. rewrite <- eqf_iff in H0.
  rewrite diff_comm, <- H0. auto.
Qed.

Theorem diff_non_sorted_mono {A: Type} `{Diff A} (l: list A) :
  permutation (from_diff (to_diff l)) l.
Proof.
  unfold to_diff.
  assert ((from_diff (to_diff_sorted (mergeSort ord l))) = (mergeSort ord l)).
  { apply diff_mono. apply mergeSort_is_sorted. }
  rewrite H0, perm_sym. apply mergeSort_is_perm.
Qed.

Lemma diff_sorted {A: Type} `{Diff A} (l: DiffList A) :
  Sorted (from_diff l).
Proof.
  destruct l as [(a & l)|]; cbn.
  - revert a. induction l; cbn. 
    + constructor.
    + intros h. destruct l; cbn in *.
      * constructor; try constructor. apply eqf_iff. rewrite diff_comm, <- diff_def; auto.
      * constructor; auto. cbn. apply eqf_iff. rewrite diff_comm, <- diff_def; auto.
  - constructor.
Qed.

Theorem DiffList_is_unique {A: Type} `{Diff A} (l l': DiffList A) :
  permutation (from_diff l) (from_diff l') -> l = l'.
Proof.
  intro perm. rewrite <- (diff_epi l), <- (diff_epi l'). f_equal. 
  apply sorted_unique_representation; auto; apply diff_sorted.
Qed.

Theorem DiffList_is_unique' {A: Type} `{Diff A} (l l': list A) :
  permutation l l' -> to_diff l = to_diff l'.
Proof.
  intro perm. apply DiffList_is_unique. apply (perm_trans _ l); [| apply (perm_trans _ l')].
  - apply diff_non_sorted_mono.
  - auto.
  - apply perm_sym. apply diff_non_sorted_mono.
Qed.



Fixpoint add_to_diff' {A: Type} `{Diff A} (x: A) (h: A) (l: list D) : list D :=
match l with
| [] => [diff h x]
| (d :: l') => if ord x (add h d)
               then diff h x :: diff x (add h d) :: l'
               else d :: add_to_diff' x (add h d) l'
end.

Definition add_to_diff {A: Type} `{Diff A} (x: A) (l: DiffList A) : DiffList A :=
match l with
| None => Some (x, [])
| Some (h, l) => if ord x h
                 then Some (x, diff x h :: l)
                 else Some (h, add_to_diff' x h l)
end.




Lemma add_to_diff_adds' {A: Type} `{Diff A} (x: A) : 
  forall (l: list D) (h: A), x = add h (diff x h) -> 
  In x (from_diff' h (add_to_diff' x h l)).
Proof.
  intros l. induction l as [| d l']; intros h Q.
  - cbn. right. left. rewrite diff_comm. symmetry. auto.
  - cbn. destruct (eqf (add h d) (add x (diff (add h d) x))) eqn:e.
    + cbn. right. left. rewrite diff_comm; symmetry; auto.
    + cbn. rewrite <- not_eqf_iff in e. right. apply IHl'.
      rewrite diff_comm in e.
      destruct (recover x (add h d)); [contradiction |auto].
Qed.

Theorem add_to_diff_adds {A: Type} `{Diff A} (x: A) : 
  forall l: DiffList A, In x (from_diff (add_to_diff x l)).
Proof.
  intros l. destruct l as [(h & t)|].
  - cbn. destruct (eqf h (add x (diff h x))) eqn:e.
    + cbn. destruct (add_to_diff' h x t); cbn; left; auto.
    + cbn. apply add_to_diff_adds'. rewrite <- not_eqf_iff in e.
      destruct (recover x h); [| auto]. rewrite diff_comm in e.
      contradiction.
  - cbn. left. auto.
Qed.


Lemma from_diff'_length {A: Type} `{Diff A} : 
  forall (l: list D) (h: A), S (length l) = length (from_diff' h l).
Proof.
  intros l. induction l; [auto|]. intros h. cbn. 
  rewrite (IHl (add h a)). auto.
Qed.

Lemma add_to_diff_adds_lenght' {A: Type} `{Diff A} (x: A) : 
  forall (l: list D) (h: A), 2 + length l = length (from_diff' h (add_to_diff' x h l)).
Proof.
  intros l. induction l; [auto|]. intros h. cbn. 
  destruct (eqf (add h a) (add x (diff (add h a) x))).
  - cbn in *. f_equal. f_equal. apply from_diff'_length.
  - cbn in *. rewrite <- IHl. auto.
Qed.

Theorem add_to_diff_lenght {A: Type} `{Diff A} (x: A) : 
  forall l: DiffList A, S (length (from_diff l)) = length (from_diff (add_to_diff x l)).
Proof.
  intros l. destruct l as [(h & t)|].
  - cbn. destruct (eqf h (add x (diff h x))).
    + cbn. rewrite <- from_diff'_length, <- from_diff'_length. auto.
    + cbn. rewrite <- from_diff'_length, <- add_to_diff_adds_lenght'. auto.
  - cbn. auto.
Qed.


Lemma add_to_diff_preserves' {A: Type} `{Diff A} (x: A) : 
  forall (l: list D) (h: A), x = add h (diff x h) -> 
  forall y, In y (from_diff' h l) -> In y (from_diff' h (add_to_diff' x h l)).
Proof.
  induction l as [| d l']; intros h Q y I.
  - cbn in *. left. destruct I as [I | []]; auto.
  - cbn in *. destruct (eqf (add h d) (add x (diff (add h d) x))) eqn:e.
    + cbn in *. destruct I; [auto|]. right. rewrite <- eqf_iff in e. right.
      assert ((add (add h (diff h x)) (diff x (add h d))) = add h d). {
        rewrite e, <- diff_def, diff_comm, <- Q, diff_comm. auto.
      } rewrite H1. auto.
    + cbn. destruct I; [auto|]. right. apply IHl'; [| auto].
      rewrite <-not_eqf_iff in e. destruct (recover x (add h d)); [|auto].
      rewrite diff_comm in H1. contradiction.
Qed.

Theorem add_to_diff_preserves {A: Type} `{Diff A} (x: A) : 
  forall (l: DiffList A) (y: A), In y (from_diff l) ->
  In y (from_diff (add_to_diff x l)).
Proof.
  intros l. destruct l as [(h & t)|].
  - cbn. destruct (eqf h (add x (diff h x))) eqn:e.
    + cbn. intros y I. rewrite <- eqf_iff in e. 
      rewrite diff_comm, <- e. right. auto.
    + intros y I. rewrite <- not_eqf_iff in e. 
      apply add_to_diff_preserves'; [|auto].
      destruct (recover x h); [|auto]. rewrite diff_comm in H0.
      contradiction.
  - intros y I. cbn in I. destruct I.
Qed.



Fixpoint min (h: nat) (l: list nat) : nat :=
match l with
| [] => h
| (h' :: l') => if h' <=? h then min h' l' else min h l'
end.

Fixpoint sub_list (s: nat) (l: list nat) : list nat :=
match l with
| [] => []
| (h :: l') => (h - s) :: sub_list s l'
end.

Fixpoint rm_one_zero (l: list nat) : list nat :=
match l with
| [] => []
| (h :: l') => if h =? O then l' else h :: rm_one_zero l'
end.

Fixpoint select_sort' (f: nat) (prev: nat) (l : list nat) : list nat :=
match f with
| O => []
| S f' =>
  match l with
  | [] => []
  | (h :: l') => let m := min h l' in
                 let p := prev + m in
                 p :: (select_sort' f' p (rm_one_zero (sub_list m l)))
  end
end.

Definition select_sort (l : list nat) : list nat :=
  select_sort' (length l) O l.


Definition abs_diff (x y: nat) := 
match x ?= y with
| Gt => x - y
| Eq => O
| Lt => y - x
end.

Lemma inverse_comp (x y: nat) : x ?= y = comp_inv (y ?= x).
Proof.
  destruct (x ?= y) eqn:e.
  - rewrite compare_eq_iff in e. subst. rewrite compare_refl. auto.
  - rewrite <- Compare_dec.nat_compare_lt in e. symmetry. apply comp_inv_sym.
    cbn. apply Compare_dec.nat_compare_gt. lia.
  - rewrite <- Compare_dec.nat_compare_gt in e. symmetry. apply comp_inv_sym.
    cbn. apply Compare_dec.nat_compare_lt. lia.
Qed.

Lemma comp_sum (x y: nat) : x ?= x + S y = Lt.
Proof.
  apply Compare_dec.nat_compare_lt. lia.
Qed.

Global Instance nat_diff : Diff nat.
Proof.
  exists (nat) (abs_diff) (Nat.add); unfold abs_diff.
  - intros x y. rewrite (inverse_comp y x). destruct (x ?= y) eqn:e; auto.
  - destruct d.
    + rewrite add_0_r, compare_refl. auto.
    + rewrite comp_sum. lia.
  - intros x y. destruct (x ?= y) eqn:e.
    + left. rewrite add_0_r. symmetry. apply compare_eq_iff. auto.
    + left. rewrite <- Compare_dec.nat_compare_lt in e. lia.
    + right. rewrite <- Compare_dec.nat_compare_gt in e. lia.
  - intros x d. rewrite compare_refl. intros H. lia.
  - intros x y z H. destruct (x ?= z) eqn:e.
    + rewrite compare_eq_iff in e. subst. lia.
    + rewrite <- Compare_dec.nat_compare_lt in e. lia.
    + exfalso. destruct (x ?= y) eqn:e'.
      * rewrite compare_eq_iff in e'. subst. rewrite add_0_r in H.
        rewrite e in H. rewrite <- Compare_dec.nat_compare_gt in e. lia.
      * rewrite <- Compare_dec.nat_compare_gt in e.
        rewrite <- Compare_dec.nat_compare_lt in e'.
        assert (e'': y ?= z = Gt) by (apply Compare_dec.nat_compare_gt; lia).
        rewrite e'' in H. rewrite <- Compare_dec.nat_compare_gt in e''. lia.
      * rewrite <- Compare_dec.nat_compare_gt in e.
        rewrite <- Compare_dec.nat_compare_gt in e'.
        destruct (y ?= z); lia.
Qed.



