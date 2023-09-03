Require Import Lia.

Require Import Master.Lib.Algebra.

Inductive Z : Type :=
| Pos : nat -> Z
| Zero : Z
| Neg : nat -> Z.

Declare Scope Z_scope.
Delimit Scope Z_scope with Z.
Bind Scope Z_scope with Z.
Open Scope Z_scope.

Definition neg (n: Z) : Z :=
match n with
| Pos k => Neg k
| Zero => Zero
| Neg k => Pos k
end.

Definition abs (n: Z) : Z :=
match n with
| Pos k => Pos k
| Zero => Zero
| Neg k => Pos k
end.

Definition abs' (n: Z) : nat :=
match n with
| Pos k => S k
| Zero => O
| Neg k => S k
end.

Definition succ (n: Z) : Z :=
match n with
| Pos k => Pos (S k)
| Zero => Pos O
| Neg O => Zero
| Neg (S n) => Neg n
end.

Definition pred (n: Z) : Z :=
match n with
| Pos (S n) => Pos n
| Pos O => Zero
| Zero => Neg O
| Neg n => Neg (S n)
end.

Theorem one_is_zero_succ : Pos O = succ Zero.
Proof.
  cbn. trivial.
Qed.

Theorem succ_S : forall n: nat, Pos (S n) = succ (Pos n).
Proof.
  destruct n; cbn; trivial. 
Qed.

Theorem minus_one_is_zero_pred : Neg O = pred Zero.
Proof.
  cbn. trivial.
Qed.

Theorem pred_S : forall n: nat, Neg (S n) = pred (Neg n).
Proof.
  destruct n; cbn; trivial. 
Qed.

Theorem Z_ind' (P : Z -> Prop) (base: P Zero) (suc: forall z: Z, P z -> P (succ z)) 
  (pre: forall z: Z, P z -> P (pred z)) : forall z: Z, P z.
Proof.
  intro z. destruct z; [| assumption |].
  - induction n.
    + rewrite one_is_zero_succ. apply suc. assumption.
    + rewrite succ_S. apply suc. assumption.
  - induction n.
    + rewrite minus_one_is_zero_pred. apply pre. assumption.
    + rewrite pred_S. apply pre. assumption.
Qed.

Theorem Z_ind'' (P : Z -> Prop) (base: P Zero) (base_pos: P (Pos O)) (base_neg: P (Neg O))
  (suc: forall n: nat, P (Pos n) -> P (Pos (S n))) 
  (pre: forall n: nat, P (Neg n) -> P (Neg (S n))) : forall z: Z, P z.
Proof.
  intro z. destruct z.
  - induction n.
    + assumption.
    + apply suc. assumption.
  - assumption.
  - induction n.
    + assumption.
    + apply pre. assumption.
Qed.

Theorem neg_neg: forall n : Z, neg (neg n) = n.
Proof.
  intro n. destruct n; cbn; reflexivity.
Qed.

Theorem abs_impotent: forall n : Z, abs n = abs (abs n).
Proof.
  intro n. destruct n; cbn; reflexivity.
Qed.

Theorem succ_pred : forall n: Z, succ (pred n) = n.
Proof.
  intro n. destruct n; [| auto |]; now destruct n.
Qed.

Theorem pred_succ : forall n: Z, pred (succ n) = n.
Proof.
  intro n. destruct n; [| auto |]; now destruct n.
Qed.





(* add *)

Fixpoint map_n {A: Type} (n: nat) (f: A -> A) (x: A) : A :=
match n with
| O => x
| S n' => f (map_n n' f x)
end.

Definition add (a b : Z) : Z :=
match a with 
| Pos n => map_n (S n) succ b
| Zero => b
| Neg n => map_n (S n) pred b
end.

Notation "- x" := (neg x) : Z_scope.
Infix "+" := add : Z_scope.

Definition sub (a b : Z) : Z :=
  a + (- b).

Theorem add_r_zero : forall x: Z, x + Zero = x.
Proof.
  induction x using Z_ind''; cbn; [trivial | trivial | trivial |rewrite succ_S | rewrite pred_S];
  f_equal; apply IHx.
Qed.

Theorem add_r_succ : forall x y: Z, x + (succ y) = succ (x + y).
Proof.
  intros x y. induction x using Z_ind''; trivial; cbn in *.
  - rewrite pred_succ. rewrite succ_pred. trivial.
  - f_equal. apply IHx.
  - rewrite succ_pred. rewrite succ_pred in IHx. rewrite IHx. trivial.
Qed.

Theorem add_r_pred : forall x y: Z, x + (pred y) = pred (x + y).
Proof.
  intros x y. induction x using Z_ind''; trivial; cbn in *.
  - rewrite pred_succ, succ_pred. trivial.
  - rewrite pred_succ, IHx in *. trivial.
  - f_equal. apply IHx.
Qed.

Theorem add_comm: forall x y: Z, x + y = y + x.
Proof.
  intro x. induction x using Z_ind''; intro y; cbn.
  - rewrite add_r_zero. cbn. trivial.
  - rewrite one_is_zero_succ, add_r_succ, add_r_zero. trivial.
  - rewrite minus_one_is_zero_pred, add_r_pred, add_r_zero. trivial.
  - rewrite succ_S, add_r_succ. f_equal. apply IHx.
  - rewrite pred_S, add_r_pred. f_equal. apply IHx.
Qed.

Theorem neg_succ : forall x: Z, - (succ x) = pred (- x).
Proof.
  destruct x; [| auto |]; now destruct n.
Qed.

Theorem neg_pred : forall x: Z, - (pred x) = succ (- x).
Proof.
  destruct x; [| auto |]; now destruct n.
Qed.

Theorem add_pred_succ : forall x y: Z, (pred x) + (succ y) = x + y.
Proof.
  intros x y. 
  now rewrite add_r_succ, (add_comm (pred x) y), add_r_pred, succ_pred, add_comm.
Qed.

Theorem add_neg_r : forall x: Z, x + (- x) = Zero.
Proof.
  induction x using Z_ind''; trivial.
  - now rewrite succ_S, neg_succ, add_comm, add_pred_succ, add_comm.
  - now rewrite pred_S, neg_pred, add_pred_succ.
Qed.

Theorem add_neg_l : forall x: Z, (- x) + x = Zero.
Proof.
  intros x. now rewrite add_comm, add_neg_r.
Qed.


Theorem add_l_succ : forall x y: Z, (succ x) + y = succ (x + y).
Proof.
  intros x y. rewrite (add_comm (succ x) y), add_r_succ. f_equal. apply add_comm.
Qed.

Theorem add_succ_swap : forall x y: Z, x + (succ y) = (succ x) + y.
Proof.
  intros x y. rewrite add_r_succ, add_l_succ. trivial.
Qed.

Theorem add_l_pred : forall x y: Z, (pred x) + y = pred (x + y).
Proof.
  intros x y. rewrite (add_comm (pred x) y), add_r_pred. f_equal.
  apply add_comm.
Qed.

Theorem add_pred_swap : forall x y: Z, x + (pred y) = (pred x) + y.
Proof.
  intros x y. rewrite add_r_pred, add_l_pred. trivial.
Qed.

Theorem add_assoc : forall x y z: Z, (x + y) + z = x + (y + z).
Proof.
  intros x y z. induction x using Z_ind'';
  [ auto | cbn; apply add_l_succ | cbn; apply add_l_pred | ..].
  - rewrite succ_S, add_l_succ, add_l_succ, add_l_succ. f_equal. apply IHx.
  - rewrite pred_S, add_l_pred, add_l_pred, add_l_pred. f_equal. apply IHx.
Qed.

Theorem add_one : forall x: Z, x + (Pos O) = succ x.
Proof.
  intro x. rewrite one_is_zero_succ, add_r_succ, add_r_zero. trivial.
Qed.

Theorem add_minus_one : forall x: Z, x + (Neg O) = pred x.
Proof.
  intro x. now rewrite minus_one_is_zero_pred, add_r_pred, add_r_zero.
Qed.

Theorem add_neg : forall x y: Z, (- x) + (- y) =  - (x + y).
Proof.
  intros x y. induction x using Z_ind''; 
  [ trivial | cbn; symmetry; apply neg_succ | cbn; symmetry; apply neg_pred | ..].
  - now rewrite succ_S, add_l_succ, neg_succ, neg_succ, <- IHx, add_l_pred.
  - now rewrite pred_S, add_l_pred, neg_pred, neg_pred, <- IHx, add_l_succ.
Qed.

Theorem add_r_neg : forall x y: Z, x + (- y) =  - ((- x) + y).
Proof.
  intros x y. induction x using Z_ind'';
  [ trivial | cbn; now rewrite neg_pred | cbn; now rewrite neg_succ | ..].
  - now rewrite succ_S, add_l_succ, IHx, neg_succ, add_l_pred, neg_pred. 
  - now rewrite pred_S, add_l_pred, neg_pred, add_l_succ, neg_succ, IHx. 
Qed.

Theorem add_l_neg : forall x y: Z, (- x) + y =  - (x + (- y)).
Proof.
  intros x y. now rewrite add_comm, add_r_neg, add_comm.
Qed.





(* mul *)
  
Definition mul (a b: Z) : Z :=
match a with 
| Pos n => map_n (S n) (add b) Zero
| Zero => Zero
| Neg n => neg (map_n (S n) (add b) Zero)
end.

Infix "*" := mul : Z_scope.

Definition id {A: Type} (x: A) := x.

Theorem mul_r_zero : forall x: Z, x * Zero = Zero.
Proof.
  intros x. destruct x; cbn; [| auto |]; now induction n.
Qed.

Theorem mul_r_one : forall x: Z, x * (Pos O) = x.
Proof.
  induction x using Z_ind''; [auto | auto | auto | ..]; cbn.
  - rewrite succ_S. now f_equal.
  - rewrite pred_S, neg_succ. now f_equal. 
Qed.

Theorem mul_r_minus_one : forall x: Z, x * (Neg O) = - x.
Proof.
  induction x using Z_ind''; [auto | auto | auto | ..]; cbn.
  - rewrite pred_S. now f_equal.
  - rewrite succ_S, neg_pred. now f_equal.
Qed.

Theorem mul_r_succ : forall x y: Z, x * (succ y) = (x * y) + x.
Proof.
  intros x y. induction x using Z_ind''; [trivial|..]; cbn in *.
  - now rewrite add_r_zero, add_r_zero, add_one.
  - now rewrite add_r_zero, add_r_zero, add_minus_one, neg_succ.
  - rewrite IHx, add_l_succ, succ_S, add_r_succ. f_equal. 
    now rewrite add_assoc, add_assoc, add_assoc.
  - rewrite pred_S, <- add_neg, IHx, <- add_neg, <- add_neg, <- add_neg,
    add_r_pred, neg_succ, add_l_pred. f_equal.
    now rewrite add_assoc, add_assoc, add_assoc.
Qed.

Theorem mul_r_pred : forall x y: Z, x * (pred y) = (x * y) + (- x).
Proof.
  intros x y. induction x using Z_ind''; [trivial| ..]; cbn in *.
  - now rewrite add_r_zero, add_r_zero, add_minus_one.
  - now rewrite add_r_zero, add_r_zero, add_one, neg_pred.
  - rewrite IHx, add_l_pred, pred_S, add_r_pred. f_equal. 
    now rewrite add_assoc, add_assoc, add_assoc.
  - rewrite succ_S, <- add_neg, IHx, <- add_neg,  <- add_neg, <- add_neg,
    add_r_succ, neg_pred, add_l_succ. f_equal.
    now rewrite add_assoc, add_assoc, add_assoc.
Qed.

Theorem mul_comm : forall x y: Z, x * y = y * x.
Proof.
  intros x y. induction x using Z_ind''.
  - now rewrite mul_r_zero.
  - cbn. now rewrite mul_r_one, add_r_zero.
  - cbn. now rewrite mul_r_minus_one, add_r_zero.
  - rewrite succ_S, mul_r_succ, <- IHx. cbn. rewrite add_assoc.
    f_equal. apply add_comm.
  - rewrite pred_S, mul_r_pred, <- IHx. cbn.
    now rewrite <- add_neg, <- add_neg, add_comm.
Qed.

Theorem mul_l_succ : forall x y: Z, (succ x) * y = (x * y) + y.
Proof.
  intros x y. now rewrite mul_comm, mul_r_succ, (mul_comm x y).
Qed.

Theorem mul_l_pred : forall x y: Z, (pred x) * y = (x * y) + (- y).
Proof.
  intros x y. now rewrite mul_comm, mul_r_pred, (mul_comm x y).
Qed.

Theorem mul_r_neg : forall x y: Z, x * (- y) = - (x * y).
Proof.
  intros x y. induction x using Z_ind'; [auto | auto | auto |..].
  - now rewrite mul_l_succ, mul_l_succ, IHx, add_neg.
  - now rewrite mul_l_pred, mul_l_pred, IHx, add_r_neg, neg_neg.
Qed.

Theorem mul_l_neg : forall x y: Z, (- x) * y = - (x * y).
Proof.
  intros x y. now rewrite mul_comm, mul_r_neg, mul_comm.
Qed.

Theorem mul_neg : forall x y: Z, (- x) * (- y) = x * y.
Proof.
  intros x y. now rewrite mul_r_neg, mul_l_neg, neg_neg.
Qed.

Theorem mul_neg_swap : forall x y: Z, (- x) * y = x * (- y).
Proof.
  intros x y. now rewrite mul_r_neg, mul_l_neg.
Qed.

Theorem mul_l_dist : forall x y z: Z, x * (y + z) = (x * y) + (x * z).
Proof.
  intros x y z. induction x using Z_ind'; [auto | auto | auto |..].
  - now rewrite mul_l_succ, mul_l_succ, mul_l_succ, IHx, add_assoc, add_assoc,
    (add_comm (mul x z) (add y z)), (add_comm (mul x z) z), add_assoc.
  - now rewrite mul_l_pred, mul_l_pred, mul_l_pred, IHx, add_assoc, add_assoc,
    (add_comm (neg y) (add (mul x z) (neg z))), (add_comm y z), add_assoc, add_neg.
Qed.

Theorem mul_r_dist : forall x y z: Z, (y + z) * x = (y * x) + (z * x).
Proof.
  intros x y z. now rewrite (mul_comm (y + z) x), (mul_comm y x), (mul_comm z x), mul_l_dist.
Qed.

Theorem mul_assoc : forall x y z: Z, (x * y) * z = x * (y * z).
Proof.
  intros x y z. induction x using Z_ind'; [auto | auto | auto |..].
  - rewrite mul_l_succ, mul_l_succ, mul_comm, mul_l_dist, <- IHx. 
    f_equal; apply mul_comm.
  - rewrite mul_l_pred, mul_l_pred, add_r_neg, mul_l_neg, add_r_neg. 
    f_equal. rewrite mul_comm, mul_l_dist. f_equal.
    + rewrite <- IHx, mul_r_neg. f_equal. apply mul_comm.
    + apply mul_comm.
Qed.


(* additional operations on know sign numbers *)
Lemma pos_add (n m: nat) : add (Pos n) (Pos m) = Pos (S (n + m)).
Proof.
  induction n; [auto|]. now rewrite succ_S, add_l_succ, IHn, <-succ_S.
Qed.

Lemma neg_add (n m: nat) : add (Neg n) (Neg m) = Neg (S (n + m)).
Proof.
  induction n; [auto|]. now rewrite pred_S, add_l_pred, IHn, <-pred_S.
Qed.

Lemma pos_mul (n m: nat) : Pos n * Pos m = Pos (S n * S m - 1).
Proof.
  induction n.
  - cbn [mul map_n]. rewrite add_r_zero. f_equal. lia.
  - rewrite succ_S, mul_l_succ, IHn, pos_add. f_equal. lia.
Qed.

Lemma pos_neg_mul (n m: nat) : Pos n * Neg m = Neg (S n * S m - 1).
Proof.
  induction n.
  - cbn [mul map_n]. rewrite add_r_zero. f_equal. lia.
  - rewrite succ_S, mul_l_succ, IHn, neg_add. f_equal. lia.
Qed.

Lemma neg_pos_mul (n m: nat) : Neg n * Pos m = Neg (S n * S m - 1).
Proof.
  rewrite mul_comm, pos_neg_mul. f_equal. lia.
Qed.

Lemma neg_mul (n m: nat) : Neg n * Neg m = Pos (S n * S m - 1).
Proof.
  induction n.
  - cbn [mul map_n]. rewrite add_r_zero. cbn. f_equal. lia.
  - rewrite pred_S, mul_l_pred, IHn. cbn [neg]. rewrite pos_add. f_equal. lia.
Qed.


(* Algebra instances *)

Global Program Instance Z_is_Group : Group Z := {
  zero  := Zero;
  op    := add;
  inv   := neg;
}.

Next Obligation. apply add_r_zero. Defined.
Next Obligation. apply add_neg_l. Defined.
Next Obligation. apply add_neg_r. Defined.
Next Obligation. apply add_assoc. Defined.

Global Program Instance Z_is_Ring : Ring Z := {
  one  := Pos O;
  mul  := mul;
}.

Next Obligation. apply add_comm. Defined.
Next Obligation. apply add_r_zero. Defined.
Next Obligation. apply mul_r_one. Defined.
Next Obligation. apply mul_assoc. Defined.
Next Obligation. apply mul_l_dist. Defined.
Next Obligation. apply mul_r_dist. Defined.


Global Program Instance Z_is_RingComm : RingComm Z.

Next Obligation. apply mul_comm. Defined.
  


