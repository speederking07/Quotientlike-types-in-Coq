Require Import Master.Lib.Normalization.
Require Import Master.Lib.EqDec.
Require Import Master.Lib.HoTT.
Require Import Master.Lib.LinearOrder.
Require Import Master.Lib.Sorted.
Require Import Master.Lib.MergeSort.



Theorem mergeSort_is_normalization (A: Type) `{LinearOrder A} : 
  normalzation (mergeSort ord).
Proof.
  unfold normalzation. intros x. apply sorted_unique_representation.
  - apply mergeSort_is_perm.
  - apply mergeSort_is_sorted.
  - apply mergeSort_is_sorted.
Qed.

Definition FiniteMultiSet (A: Type) `{LO: LinearOrder A} : Type :=
  QuotientNorm (A := list A) (N := mergeSort_is_normalization A) (mergeSort ord).

Definition make_FiniteMultiSet {A: Type} `{LO: LinearOrder A} (l: list A) := 
  make_QN (mergeSort ord) l (N := mergeSort_is_normalization A).

Definition getElems {A: Type} `{LO: LinearOrder A} (m: FiniteMultiSet A) : list A :=
  val m.

Lemma permutaion_sort_is_sort_eq {A: Type} `{LO: LinearOrder A} (l l': list A) :
  mergeSort ord l = mergeSort ord l' <-> permutation l l'.
Proof.
  split.
  - intros. apply (perm_trans _ (mergeSort ord l)). 
    + apply mergeSort_is_perm. 
    + rewrite H, perm_sym. apply mergeSort_is_perm.
  - intros P. apply sorted_unique_representation; 
    [| apply mergeSort_is_sorted | apply mergeSort_is_sorted].
    apply (perm_trans _ l).
    + rewrite perm_sym. apply mergeSort_is_perm.
    + apply (perm_trans _ l'); [auto|]. apply mergeSort_is_perm.
Qed.

Theorem unique_repr_FiniteMultiSet {A: Type} `{LO: LinearOrder A} (m m': FiniteMultiSet A) :
  permutation (getElems m) (getElems m') -> m = m'.
Proof.
  intros H. apply quotient_unique_representation. unfold norm_equiv, getElems in *.
  rewrite permutaion_sort_is_sort_eq. auto.
Qed.

Theorem all_repr_FiniteMultiSet {A: Type} `{LO: LinearOrder A} (m: list A) :
  permutation m (getElems (make_FiniteMultiSet m)).
Proof.
  cbn. apply mergeSort_is_perm.
Qed. 
