Require Import Setoid.
Require Import Coq.Lists.List.
Require Import Bool.
Require Import Coq.Program.Equality.
Require Import Lia.
Import ListNotations.
Require Import Lib.Sorted.
Require Import Lib.EqDec.
Require Import Lib.MergeSort.

Class Diff (A: Type) `{E: EqDec A} := {
  D: Type;
  diff: A -> A -> D;
  add: A -> D -> A;

  diff_comm: forall x y, diff x y = diff y x;
  diff_def: forall x d, d = diff x (add x d);
  (* add_zero: forall x y, x = add x (diff y y); *)
  recover: forall x y, y = add x (diff x y) \/ x = add y (diff x y);
  add_mono: forall x y d, add x d = add y d -> x = y;
  diff_not_sym: forall x y, y = add x (diff x y) -> x = add y (diff x y) -> x = y;
  diff_trans: forall x y z, z = add (add x (diff x y)) (diff y z) -> z = add x (diff x z);
}.

Theorem diff_uniq(A: Type) `{Diff A}: forall x d d', add x d = add x d' -> d = d'.
Proof.
  intros x d d' Heq. rewrite (diff_def x), <- Heq, <- diff_def; auto.
Qed.

Global Instance Diff_is_LO (A: Type) `{D: Diff A} : LinearOrder A.
Proof.
  exists (fun x y => eqf y (add x (diff y x))).
  - intros x. destruct (eqf_leibniz x (add x (diff x x))); auto. 
    destruct (recover x x); rewrite <- H in n; contradiction.
  - intros x y. rewrite (diff_comm y), <- eqf_iff, <- eqf_iff. intros e e'. apply diff_not_sym; auto.
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

Fixpoint to_diff' {A: Type} `{Diff A} (p: A) (l: list A) : list D :=
  match l with
  | [] => []
  | (h :: t) => diff p h :: to_diff' h t
  end.

Definition to_diff {A: Type} `{Diff A} (l: list A) : DiffList A :=
  match l with
  | [] => None
  | (h :: t) => Some (h, to_diff' h t)
  end.

Definition to_diff_non_sorted {A: Type} `{Diff A} (l: list A) : DiffList A :=
  to_diff (mergeSort ord l).

Theorem diff'_epi {A: Type} `{Diff A} (l: list D) (x h: A) :
  to_diff' x (from_diff' h l) = (diff x h :: l).
Proof.
  revert x h. induction l; auto. intros x h. cbn. f_equal. 
  assert (a :: l = diff h (add h a) :: l) by (rewrite <- diff_def; auto). rewrite H0.
  apply IHl.
Qed.

Theorem diff_epi {A: Type} `{Diff A} (l: DiffList A) :
  to_diff (from_diff l) = l.
Proof.
  destruct l as [(a & l)|]; cbn; auto.
  revert a. induction l; cbn; intro h; auto.
  f_equal; f_equal. rewrite diff'_epi, <- diff_def. auto.
Qed.

Theorem diff_mono {A: Type} `{Diff A} (l: list A) :
  Sorted l -> from_diff (to_diff l) = l.
Proof.
  intros s. induction s; auto. cbn in *. f_equal. rewrite <- eqf_iff in H0.
  rewrite diff_comm, <- H0. auto.
Qed.

Theorem diff_non_sorted_mono {A: Type} `{Diff A} (l: list A) :
  permutation (from_diff (to_diff_non_sorted l)) l.
Proof.
  unfold to_diff_non_sorted.
  assert ((from_diff (to_diff (mergeSort ord l))) = (mergeSort ord l)).
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




