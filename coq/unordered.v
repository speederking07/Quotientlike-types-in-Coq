Require Import StrictProp.
Print StrictProp.
Print True.
Check True : Prop.
Definition twoElem (A: Type): SProp :=
  Squash (exists x y: A, x <> y /\ (forall z: A, x = z \/ y = z)).

Record UPair (A: Type) := {
   X : Type;
   hasTwo : twoElem X;
   elem : X -> A
}.

Theorem bool_two_elem : twoElem bool.
Proof.
  unfold twoElem. constructor; exists true, false.
  split.
  - discriminate.
  - destruct z; auto.
Qed.

Definition createUPair {A: Type} (a b: A): UPair A := {|
  X := bool;
  hasTwo := bool_two_elem;
  elem := fun x => if x then a else b
|}.

Print pairFunc.

 
Definition get {A: Type} (p :UPair A): A :=
  match p with
  | pair _ f  => f bool bool_two_elem true
  end.
