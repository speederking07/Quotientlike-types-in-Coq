Require Import Recdef.
Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Setoid.

Inductive Qplus : Type :=
| One : Qplus
| N   : Qplus -> Qplus
| D   : Qplus -> Qplus.

Definition Q : Type := (nat * nat).

Definition num (q: Q) := let (n, _) := q in n.
Definition den (q: Q) := let (_, d) := q in d.

Function qplus_c' (p q n: nat) : Qplus :=
match n with
| O    => One
| S n' => match compare p q with
          | Eq => One
          | Gt => N (qplus_c' (p - q) q n')
          | Lt => D (qplus_c' p (q - p) n')
          end
end.

Function qplus_c (x: Q) : Qplus :=
  let (p, q) := x in qplus_c' p q ((p + q) / gcd p q).

Function qplus_i (x : Qplus) : Q :=
match x with
| One  => (1, 1)
| N x' => let (p, q) := qplus_i x' in (p + q, q)
| D x' => let (p, q) := qplus_i x' in (p, p + q)
end.

Definition valid (x: Q) := num x > 0 /\ den x > 0.

Lemma pos_mul_comp : forall a b k: nat, ((S k * a) ?= (S k * b)) = (a ?= b).
Proof.
  intros a b k. induction k.
  - rewrite Nat.mul_1_l, Nat.mul_1_l. reflexivity.
  - destruct (a ?= b) eqn:P.
    + rewrite Nat.compare_eq_iff in *. lia.
    + rewrite Nat.compare_lt_iff in *. lia.
    + rewrite Nat.compare_gt_iff in *. lia.
Qed.

Lemma mul_exp : forall n k: nat, n + k * n = S k * n.
Proof.
  intros n k. cbn. auto.
Qed.

Theorem qplus_c'_mul_pos : forall p q n k: nat,
  qplus_c' (S k * p) (S k * q) n = qplus_c' p q n.
Proof.
  intros p q n. revert p q. induction n; intros p q k; auto.
  simpl. rewrite <- (IHn p (q - p) k), <- (IHn (p - q) q k), <- (pos_mul_comp p q k).
  simpl. destruct (p + k * p ?= q + k * q) eqn:P; auto.
  - f_equal. f_equal. assert (p < q).
    + rewrite Compare_dec.nat_compare_lt, <- P. symmetry.
      rewrite mul_exp, mul_exp. apply pos_mul_comp.
    + rewrite <- Compare_dec.nat_compare_lt in P. lia.
  - f_equal. f_equal. assert (p > q).
    + rewrite Compare_dec.nat_compare_gt, <- P. symmetry. 
      rewrite mul_exp, mul_exp. apply pos_mul_comp.
    + rewrite <- Compare_dec.nat_compare_gt in P. lia.
Qed.

Lemma fuel_for_qplus_c (p q: nat) :
  qplus_c' p q ((p + q) / gcd p q) = qplus_c' p q (S ((p + q) / gcd p q)).
Proof.
  admit.
Admitted.

Lemma fuel_for_qplus_c' (p q f: nat) :
  ((p + q) / gcd p q) <= f -> qplus_c' p q ((p + q) / gcd p q) = qplus_c' p q f.
Proof.
  admit.
Admitted.

Lemma qplus_valid (x: Qplus) : valid (qplus_i x).
Proof.
  unfold valid. induction x; auto.
  - cbn. destruct (qplus_i x). cbn in *. lia.
  - cbn. destruct (qplus_i x). cbn in *. lia.
Qed.

Notation "( x | y )" := (Nat.divide x y) (at level 0).

Definition CoPrime (a b: nat) := gcd a b = 1.

Lemma CoPrime_symm (a b: nat) : CoPrime a b -> CoPrime b a.
Proof.
  unfold CoPrime. rewrite Nat.gcd_comm. auto.
Qed.

Definition norm (x: Q) := CoPrime (num x) (den x).



Lemma zero_div (x: nat) : x / 0 = 0.
Proof.
  induction x; auto.
Qed.

Lemma gcd_ge (n m: nat): (n + m) / gcd n m <= (n + m + m) / gcd (n + m) m.
Proof.
  assert (gcd n m = gcd (n + m) m).
  { rewrite Nat.gcd_comm, (Nat.gcd_comm (n + m)). symmetry. apply Nat.gcd_add_diag_r. }
  rewrite <- H. destruct (gcd n m).
  - rewrite zero_div, zero_div. lia.
  - apply Nat.div_le_mono; lia.
Qed.
 
Theorem qplus_mono (x : Qplus) :  qplus_c (qplus_i x) = x.
Proof.
  unfold qplus_c. induction x; auto.
  - cbn. destruct (qplus_i x) eqn: e. rewrite fuel_for_qplus_c. cbn.
    assert (num (qplus_i x) > 0 /\ den (qplus_i x) > 0) by apply qplus_valid.
    rewrite e in H. cbn in H. inversion H. assert (n + n0 ?= n0 = Gt).
    + rewrite Nat.compare_gt_iff. lia.
    + rewrite H2, <- IHx. rewrite Nat.add_sub. f_equal. symmetry. apply fuel_for_qplus_c'. apply gcd_ge.
  - cbn. destruct (qplus_i x) eqn: e. rewrite fuel_for_qplus_c. cbn.
    assert (num (qplus_i x) > 0 /\ den (qplus_i x) > 0) by apply qplus_valid.
    rewrite e in H. cbn in H. inversion H. assert (n ?= n + n0 = Lt).
    + rewrite Nat.compare_lt_iff. lia.
    + rewrite H2, <- IHx. rewrite (Nat.add_comm n n0), Nat.add_sub. f_equal.
      symmetry. rewrite (Nat.add_comm n0 n), Nat.add_assoc. apply fuel_for_qplus_c'.
      rewrite (Nat.add_comm n n0), (Nat.gcd_comm n n0), (Nat.gcd_comm n (n0 + n)).
      rewrite <- Nat.add_assoc, (Nat.add_comm n n0), Nat.add_assoc, (Nat.add_comm n n0). apply gcd_ge.
Qed.

Theorem qplus_c_mul_pos : forall p q k: nat,
  qplus_c (S k * p, S k * q) = qplus_c (p, q).
Proof.
  intros p q k. unfold qplus_c. 
  assert (((S k * p + S k * q) / gcd (S k * p) (S k * q)) = ((p + q) / gcd p q)). 
  - rewrite Nat.gcd_mul_mono_l. remember (gcd p q) as g. destruct g.
    + rewrite Nat.mul_0_r, zero_div, zero_div. auto.
    + rewrite <- Nat.div_div; try lia. rewrite Nat.mul_comm, Nat.div_add_l, Nat.mul_comm; try lia. 
      rewrite Nat.div_mul; lia.
  - rewrite H. apply qplus_c'_mul_pos.
Qed.




Definition frac_eq (a b : Q) := num a * den b = num b * den a.

Theorem frac_eq_relf (x: Q) `{valid x} : frac_eq x x.
Proof.
  destruct x. unfold frac_eq. lia.
Qed.

Theorem frac_eq_symm (x y: Q) : frac_eq x y -> frac_eq y x.
Proof.
  destruct x, y. unfold frac_eq. lia.
Qed.

Theorem coprime_equiv (a b c d: nat) : CoPrime a b -> CoPrime c d ->
  a * d = c * b -> a = c.
Proof.
  unfold CoPrime. intros C0 C1 E. 
  assert (a | c). {
    apply (Nat.gauss a b c); auto. exists d. lia.
  }
  assert (d | b). {
    rewrite Nat.gcd_comm in C1. apply (Nat.gauss d c b); auto. exists a. lia.
  }
  destruct H as (k & H). destruct H0 as (k' & H'). rewrite H in E. rewrite H' in E.
  destruct a; destruct d; try lia.
  - rewrite Nat.mul_0_r in *. subst. rewrite Nat.gcd_0_r in *. lia.
  - rewrite (Nat.mul_comm k), <- Nat.mul_assoc, Nat.mul_cancel_l in E; try lia.
    rewrite Nat.mul_assoc, <- (Nat.mul_1_l (S d)), Nat.mul_assoc, Nat.mul_cancel_r in E; try lia.
    rewrite Nat.mul_1_r in E. assert (k = 1 /\ k' = 1). {
      apply Mult.mult_is_one. auto.
    }
    destruct H0 as (k1 & k'1). subst. lia.
Qed.

Lemma id_mul_is_1 (a b : nat) : a > 0 -> a = b * a -> b = 1.
Proof.
  intros P H. destruct a.
  - lia.
  - destruct b.
    + cbn in *. inversion H.
    + lia.
Qed.

Lemma mul_div (a b : nat) : (b | a) -> a / b * b = a.
Proof.
  intros h. destruct h as (k & H). rewrite H. destruct b.
  - cbn. rewrite Nat.mul_0_r. auto.
  - rewrite Nat.div_mul; auto.
Qed.

Theorem gcd_equiv (a b c d: nat) : a > 0 -> c > 0 -> 
  a * d = c * b -> a * gcd c d = c * gcd a b.
Proof.
  assert (gcd a b | a) by apply Nat.gcd_divide_l.
  assert (gcd c d | c) by apply Nat.gcd_divide_l.
  destruct H as (n & Ha). destruct H0 as (m & Hc).
  intros H aP cP. remember (gcd a b) as g. remember (gcd c d) as h. rewrite Ha, Hc.
  assert (g <> 0) by (destruct g; lia).
  assert (h <> 0) by (destruct h; lia).
  assert (n = m). {
    assert (n = a / g). 
    { rewrite <- (Nat.mul_cancel_r _ _ g); auto. rewrite mul_div; try lia. subst. apply Nat.gcd_divide_l. }
    assert (m = c / h). 
    { rewrite <- (Nat.mul_cancel_r _ _ h); auto. rewrite mul_div; try lia. subst. apply Nat.gcd_divide_l. }
    apply (coprime_equiv _ (b / g) _ (d / h)).
    - subst. unfold CoPrime. apply Nat.gcd_div_gcd; auto.
    - subst. unfold CoPrime. apply Nat.gcd_div_gcd; auto.
    - rewrite Ha, Hc in cP. rewrite <- (Nat.mul_cancel_r _ _ h), <- (Nat.mul_cancel_r _ _ g); auto.
      rewrite <- (Nat.mul_assoc n _ h), mul_div; try (subst; apply Nat.gcd_divide_r). 
      rewrite <- (Nat.mul_assoc _ h g), (Nat.mul_comm h g), Nat.mul_assoc, <- (Nat.mul_assoc m _ g).
      rewrite mul_div; try (subst; apply Nat.gcd_divide_r). lia. 
  } lia.
Qed.

Theorem frac_div (a b c d z: nat) :
  a * d = c * b -> (z | c) -> (z | d) -> a * (d / z) = (c / z) * b.
Proof. 
  intros e nd dd. destruct z.
  - cbn. rewrite <- mult_n_O. auto.
  - rewrite (Nat.mul_comm _ b), <- Nat.divide_div_mul_exact, <- Nat.divide_div_mul_exact; auto.
    f_equal. lia.
Qed.

Theorem co_prime_gcd (a b: nat) :
  a > 0 -> CoPrime (a / gcd a b) (b / gcd a b).
Proof.
  intros Pa. apply Nat.gcd_div_gcd; auto. destruct (gcd a b) eqn: H; try lia.
  assert (a = 0) by (apply (Nat.gcd_eq_0_l a b); auto). lia. 
Qed.

Theorem frac_eq_trans (x y z: Q) : valid x -> valid y -> valid z -> 
  frac_eq x y -> frac_eq y z -> frac_eq x z.
Proof.
  destruct x as (x & x'). destruct y as (y & y'). destruct z as (z & z').
  unfold valid, frac_eq. cbn. intros (Px & Px') (Py & Py') (Pz & Pz') H H'.
  assert (x * gcd y y' = y * gcd x x') by (apply gcd_equiv; auto).

  admit.
  
Admitted.





