Require Import Lib.Normalization.
Require Import Lib.EqDec.
Require Import Lib.HoTT.
Require Import Lib.LinearOrder.
Require Import Lib.Deduplicated.
Require Import Lib.DedupSort.



Theorem dedupSort_is_normalization (A: Type) `{LinearOrder A} : 
  normalzation dedupSort.
Proof.
  unfold normalzation. intros x. apply dedupsorted_unique_representation. Search dedupSort.
  - apply same_elements_dedupSort.
  - apply sorted_dedupSort.
  - apply sorted_dedupSort.
  - apply dedup_dedupSort.
  - apply dedup_dedupSort.
Qed.

Definition FiniteSet (A: Type) `{LO: LinearOrder A} : Type :=
  QuotientNorm (A := list A) (N := dedupSort_is_normalization A) dedupSort.

Definition make_FiniteSet {A: Type} `{LO: LinearOrder A} (l: list A) := 
  make_QN dedupSort l (N := dedupSort_is_normalization A).

Definition getElems {A: Type} `{LO: LinearOrder A} (m: FiniteSet A) : list A :=
  val m.

Lemma dedupSort_is_sort_elem_eq {A: Type} `{LO: LinearOrder A} (l l': list A) :
  dedupSort l = dedupSort l' <-> Elem_eq l l'.
Proof.
  split.
  - intros H. apply (Elem_eq_trans (dedupSort l)). 
    + apply same_elements_dedupSort.
    + rewrite H, Elem_eq_sym. apply same_elements_dedupSort.
  - intros H. apply dedupsorted_unique_representation; 
    [| apply sorted_dedupSort | apply sorted_dedupSort | apply dedup_dedupSort
     | apply dedup_dedupSort ].
    apply (Elem_eq_trans l).
    + rewrite Elem_eq_sym. apply same_elements_dedupSort.
    + apply (Elem_eq_trans l'); [auto|]. apply same_elements_dedupSort.
Qed.

Theorem unique_repr_FiniteSet {A: Type} `{LO: LinearOrder A} (m m': FiniteSet A) :
  Elem_eq (getElems m) (getElems m') -> m = m'.
Proof.
  intros H. apply quotient_unique_representation. unfold norm_equiv, getElems in *.
  rewrite dedupSort_is_sort_elem_eq. auto.
Qed.

Theorem all_repr_FiniteMultiSet {A: Type} `{LO: LinearOrder A} (m: list A) :
  Elem_eq m (getElems (make_FiniteSet m)).
Proof.
  cbn. apply same_elements_dedupSort.
Qed.