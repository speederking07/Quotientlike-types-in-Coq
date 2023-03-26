Require Import Setoid.

Class Group (A : Type) := GroupDef {
  zero     : A;
  op       : A -> A -> A;
  inv      : A -> A;
  l_op_id  : forall x: A, op zero x = x;
  r_op_id  : forall x: A, op x zero = x;
  l_op_inv : forall x: A, op (inv x) x = zero;
  r_op_inv : forall x: A, op x (inv x) = zero;
  op_assoc : forall x y z: A, op (op x y) z = op x (op y z);
}.

Definition sub {A: Type} `{Group A} (x y: A) := op x (inv y).

Lemma op_sub {A: Type} `{Group A} (x y : A) : op (sub x y) y = x.
Proof.
  unfold sub. rewrite op_assoc. rewrite l_op_inv. rewrite r_op_id. auto.
Qed.

Lemma sub_op {A: Type} `{Group A} (x y : A) : sub (op x y) y = x.
Proof.
  unfold sub. rewrite op_assoc. rewrite r_op_inv. rewrite r_op_id. auto.
Qed.

Lemma group_equation_l_simp {A: Type} `{Group A} (a b c : A) : op a b = op a c -> b = c.
Proof.
  intro H0. assert (op (inv a) (op a b) = op (inv a) (op a c)).
  - rewrite H0. auto.
  - rewrite <- op_assoc, <- op_assoc, l_op_inv, l_op_id, l_op_id in H1. auto.
Qed.

Lemma group_equation_r_simp {A: Type} `{Group A} (a b c : A) : op a c = op b c -> a = b.
Proof.
  intro H0. assert (op (op a c) (inv c) = op (op b c) (inv c)).
  - rewrite H0. auto.
  - rewrite op_assoc, op_assoc, r_op_inv, r_op_id, r_op_id in H1. auto.
Qed.

Lemma sub_zero_uniq {A: Type} `{Group A} (x y: A) : sub x y = zero -> x = y.
Proof.
  unfold sub. rewrite <- (r_op_inv y). intros H0. 
  apply group_equation_r_simp with (c := inv y). auto.
Qed.

Lemma group_op_inv {A: Type} `{Group A} (x y: A) : inv (op x y) = op (inv y) (inv x).
Proof.
  unfold sub. apply group_equation_l_simp with (a := y). 
  rewrite <- op_assoc, r_op_inv, l_op_id.
  apply group_equation_l_simp with (a := x).
  rewrite r_op_inv, <- op_assoc, r_op_inv. auto.
Qed.





Class Field (A : Type) `{Group A} := FieldDef {
  one       : A;
  mul       : A -> A -> A;
  mul_inv   : A -> A;
  op_comm   : forall x y: A, op x y = op y x;
  mul_comm  : forall x y: A, mul x y = mul y x;
  l_mul_id  : forall x: A, mul one x = x;
  r_mul_id  : forall x: A, mul x one = x;
  l_mul_inv : forall x: A, mul (mul_inv x) x = one;
  r_mul_inv : forall x: A, mul x (mul_inv x) = one;
  mul_assoc : forall x y z: A, mul (mul x y) z = mul x (mul y z);
  distr     : forall x y z: A, mul x (op y z) = op (mul x y) (mul x z);
}.

Lemma field_zero_mul_l {A: Type} `{Field A} (x: A) : mul x zero = zero.
Proof.
  assert (zero = op (mul x (op zero one)) (inv x)). {
    rewrite l_op_id, r_mul_id, r_op_inv. auto.
  } 
  rewrite H1 at 2. rewrite distr, r_mul_id, op_assoc, r_op_inv, r_op_id. auto.
Qed.







