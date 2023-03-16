Require Import Coq.Program.Equality.

Inductive List (A: Type) : nat -> Type :=
  | Nil : List A 0
  | Cons : forall n: nat,  A -> List A n -> List A (S n).

Arguments Nil {A}.
Arguments Cons {A n}.

Definition len {A: Type} {n: nat} (l: List A n) : nat := n.

Theorem len_ok : forall A: Type, forall n : nat, forall l : List A n, forall a : A, S (len l) = len (Cons a l).
Proof.
  intros. cbv. trivial.
Qed.

Theorem o_means_empty : forall A: Type, forall l: List A O, l = Nil.
Proof.
  intros A l. dependent destruction l. trivial.
Qed.

Inductive UList (A: Type) : Type :=
  | UNil : UList A
  | UCons : forall l : UList, forall a : A, Unique a l -> UList A
with Unique {A : Type} (a: A) (l : UList A) : Prop :=
  | UniqNil : Unique l a
  | UniqCons : forall h : A, forall l : UList A, Unique l -> h <> a -> Unique a (UCons l h).


Inductive SEvenList (A: Type) (ord : A -> A -> bool) :=
  | SEvenNil : SEvenList A ord
  | SEvenCons : forall a: A, forall l : SOddList A ord,
       l = SOddCons h t -> ord a h = true -> SEvenList A ord
with SOddList (A: Type) (ord : A -> A -> bool) :Type :=
  | SOddCons : forall a : A, forall l : SEvenList A ord,
      (l = SEvenNil A ord \/ (l = SEvenCons h t /\ ord a h = true)) -> SOddList A ord.
