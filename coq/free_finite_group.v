Require Import EqNat.
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.

Record fin (n : nat) := Fin {
  val : nat;
  bound : val <= n;
}.

Arguments val {n}.
Arguments bound {n}.

Definition fin_eq {n: nat} (x y : fin n) := Nat.eqb (val x) (val y).
Notation "x =? y" := (fin_eq x y) (at level 10).

Inductive FreeGroup (n: nat) :=
| GNil  : FreeGroup n
| GCons : bool -> fin n -> FreeGroup n -> FreeGroup n.

Arguments GCons {n}.
Arguments GNil {n}.

Fixpoint norm_stack {n: nat} (x y : FreeGroup n) : FreeGroup n :=
match x, y with
| _, GNil                      => x
| GCons b v x', GCons b' v' y' => if (xorb b b') && (v =? v')  
                                  then norm_stack x' y'
                                  else norm_stack (GCons b' v' x) y'
| _, GCons b v y'              => norm_stack (GCons b v x) y'
end.

Definition norm {n: nat} (x: FreeGroup n) : FreeGroup n := norm_stack GNil x.

Lemma zero_leq_two : 0 <= 2. 
Proof. auto. Qed.

Lemma one_leq_two : 1 <= 2. 
Proof. auto. Qed.

Lemma two_leq_two : 2 <= 2. 
Proof. auto. Qed.

Definition zero := Fin 2 0 zero_leq_two.
Definition one := Fin 2 1 one_leq_two.
Definition two := Fin 2 2 two_leq_two.

Inductive Normalized {n: nat} : FreeGroup n -> Prop :=
| NNil  : Normalized GNil
| NSing : forall (b : bool) (v : fin n), Normalized (GCons b v GNil)
| NCons : forall (b b': bool) (v v' : fin n) (x: FreeGroup n), 
           v =? v' = false \/ xorb b b' = false -> Normalized (GCons  b' v' x) ->
           Normalized (GCons b v (GCons b' v' x)).

Lemma norm_sing : forall (n: nat) (x: FreeGroup n) (b : bool) (v: fin n) , norm x = GNil -> 
  norm (GCons b v x) = (GCons b v GNil).
Proof.
  intros n x b v H. induction x.
  - cbn. reflexivity.
  - unfold norm in *. cbn in *. destruct (xorb s b && v =? f) eqn:e.
    + cbn.  

Lemma norm_stack_normalize : forall (n: nat) (x: FreeGroup n), Normalized (norm_stack GNil x).
Proof.
  intros n x. induction x.
  - cbn. constructor.
  - cbn. dependent destruction IHx.
    + 
Admitted.

Theorem norm_normalize : forall (n: nat) (x: FreeGroup n), Normalized (norm x).
Proof.
  intros n x. apply norm_stack_normalize.
Qed.


Inductive UniqFreeGroup (n: nat) :=
| Switch : fin (n - 1) -> UniqFreeGroup n -> UniqFreeGroup n
| Stay   : fin n -> UniqFreeGroup n -> UniqFreeGroup n
| Sing   : bool -> fin n -> UniqFreeGroup n
| UNil   : UniqFreeGroup n.

