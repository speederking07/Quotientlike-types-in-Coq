Fixpoint inList {A: Set} (x: A) (l: list A): Prop :=
  match l with
  | nil => False
  | cons h t => x = h \/ inList x t
  end.

Inductive UList (A: Type) : list A -> Type :=
  | UNil : UList A []
  | UCons : forall i: list A, forall l : UList A i, forall a : A, (inList a i -> False) -> UList A []