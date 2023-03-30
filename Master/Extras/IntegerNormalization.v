Require Import Integer.

Record Izomorphism (A B: Type) := Izo {
  izo_fun : A -> B;
  izo_inv : B -> A;
  izo_id  : forall x: A, izo_inv (izo_fun x) = x;
  izo_id' : forall x: B, izo_fun (izo_inv x) = x;
}.

Record Integer := Int {
  v : nat * nat;
  one_zero : let (x, y) := v in (x = O) \/ (y = O); 
}.

Fixpoint norm (x y : nat) : (nat * nat) :=
match x, y with
| S x, S y => norm x y
| _, _ => (x, y)
end.

Definition norm' (p: nat * nat) : (nat * nat) := 
  let (x, y) := p in norm x y.

Theorem norm_is_normal (p: nat * nat) : let (x, y) := (norm' p) in (x = O) \/ (y = O).
Proof.
  destruct p. revert n0. induction n.
  - cbn. left. reflexivity.
  - destruct n0.
    + cbn. right. reflexivity.
    + cbn. apply IHn.
Qed.

Theorem norm_is_impotent : forall p: nat * nat, norm' p = norm' (norm' p).
Proof.
  intro p. destruct p. revert n0. induction n; intro n'.
  - cbn. reflexivity.
  - destruct n'; cbn.
    + reflexivity.
    + apply IHn.
Qed.

Definition get_integer (p: nat * nat) : Integer := {|
  v := norm' p;
  one_zero := norm_is_normal p;
|}.

Definition Z_to_Integer' (z : Z) : nat*nat := 
match z with 
| Pos n => (S n, O)
| Zero => (O, O) 
| Neg n => (O, S n)
end.

Theorem Z_to_Integer_proof : forall z: Z, let (x, y) := (Z_to_Integer' z) in (x = O) \/ (y = O).
Proof.
  intro z. destruct z; cbn; auto.
Defined.

Definition Z_to_Integer (z : Z) : Integer := {|
  v := Z_to_Integer' z;
  one_zero := Z_to_Integer_proof z;
|}.

Definition Integer_to_Z (i : Integer) : Z :=
match v i with
| (O, O) => Zero
| (S n, O) => Pos n
| (O, S n) => Neg n
| (S n, S n') => Zero
end.