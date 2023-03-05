Require Import Recdef.
Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Setoid.

Inductive Qplus : Type :=
| One : Qplus
| N   : Qplus -> Qplus
| D   : Qplus -> Qplus.

Function qplus' (p q n: nat) : Qplus :=
match n with
| O    => One
| S n' => match compare p q with
          | Eq => One
          | Gt => N (qplus' (p - q) q n')
          | Lt => D (qplus' p (q - p) n')
          end
end.

Definition Q : Type := (nat * nat).

Function qplus (x: Q) : Qplus :=
  let (p, q) := x in qplus' (S p) (S q) ((2 + p + q) / gcd (S p) (S q)).

Function frac' (x : Qplus) : Q :=
match x with
| One  => (1, 1)
| N x' => let (p, q) := frac' x' in (S p, q)
| D x' => let (p, q) := frac' x' in (p, p + q)
end.

Function frac (x : Qplus) : Q :=
match frac' x with
| (S p, S q) => (p, q)
| _          => (O, O)
end.

Compute frac (qplus (2, 5)).

Lemma k_comp : forall a b k: nat, ((S k * a) ?= (S k * b)) = (a ?= b).
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

Theorem qplus'_mul_const : forall p q n k: nat,
  qplus' (S k * p) (S k * q) n = qplus' p q n.
Proof.
  intros p q n. revert p q. induction n; intros p q k; auto.
  simpl. rewrite <- (IHn p (q - p) k), <- (IHn (p - q) q k), <- (k_comp p q k).
  simpl. destruct (p + k * p ?= q + k * q) eqn:P; auto.
  - f_equal. f_equal. assert (p < q).
    + rewrite Compare_dec.nat_compare_lt, <- P. symmetry. 
      rewrite mul_exp, mul_exp. apply k_comp.
    + rewrite <- Compare_dec.nat_compare_lt in P. lia.
  - f_equal. f_equal. assert (p > q).
    + rewrite Compare_dec.nat_compare_gt, <- P. symmetry. 
      rewrite mul_exp, mul_exp. apply k_comp.
    + rewrite <- Compare_dec.nat_compare_gt in P. lia.
Qed.

Definition pos_frac (p q: nat) : Prop :=
  p > 0 /\ q > 0.

Definition frac_equiv (p q p' q': nat) : Prop :=
  p * q' = p' * q.

Definition normQ (p q : nat) : (nat * nat) :=
  let d := gcd p q in (p / d, q / d).

Definition frac_equiv' (p q p' q': nat) : Prop :=
  normQ p q = normQ p' q'.

Lemma frac_equiv_symm (p q p' q': nat) : 
  frac_equiv p q p' q' -> frac_equiv p' q' p q.
Proof.
  unfold frac_equiv. intros H. auto.
Qed.

Lemma frac_equiv_symm' (p q p' q': nat) : 
  frac_equiv p q p' q' -> frac_equiv q p q' p'.
Proof.
  unfold frac_equiv. lia.
Qed.

Lemma frac_equiv_trans (p q p' q' p'' q'': nat) : 
  frac_equiv p q p' q' -> frac_equiv p' q' p'' q'' -> frac_equiv p q p'' q''.
Proof.
  admit.
Admitted.

Notation "( x | y )" := (Nat.divide x y) (at level 0).

Definition CoPrime (a b: nat) := gcd a b = 1.

Lemma CoPrime_symm (a b: nat) : CoPrime a b -> CoPrime b a.
Proof.
  unfold CoPrime. rewrite Nat.gcd_comm. auto.
Qed.

Theorem frac_equiv_const_mul (p q: nat) : p > 0 -> q > 0 ->
  CoPrime (p / gcd p q) (q / gcd p q) /\ frac_equiv p q (p / gcd p q) (q / gcd p q).
Proof.
  intros P Q. split.
  - unfold CoPrime, pos_frac in *.
    assert ((gcd p q | p) /\ (gcd p q | q)) by (apply Nat.gcd_divide).
    destruct H. apply Nat.gcd_div_gcd; auto. intros G.
    rewrite G in H. destruct p; try lia. assert (S p = 0) by (apply Nat.divide_0_l; auto).
    discriminate.
  - unfold frac_equiv. assert ((gcd p q | p) /\ (gcd p q | q)) by (apply Nat.gcd_divide).
    destruct H. unfold Nat.divide in *. destruct H, H0.
    transitivity (x * gcd p q * ((x0 * gcd p q) / gcd p q)); auto.
    transitivity ((x * gcd p q) / gcd p q * (x0 * gcd p q)); auto.
    destruct (gcd p q) eqn:G.
    + lia.
    + assert (S n <> 0) by (apply Nat.neq_succ_0).
      rewrite Nat.div_mul, Nat.div_mul; auto. lia.
Qed.

Theorem coprime_equiv (a b c d: nat) : CoPrime a b -> CoPrime c d ->
  frac_equiv a b c d -> a = c.
Proof.
  unfold frac_equiv, CoPrime. intros C0 C1 E. 
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

Theorem equiv_gcd (a b c d: nat) : 
  frac_equiv a b c d -> a * gcd c d = c * gcd a b.
Proof.
  assert (gcd a b | a) by apply Nat.gcd_divide_l.
  assert (gcd c d | c) by apply Nat.gcd_divide_l.
  destruct H as (n & Ha). destruct H0 as (m & Hc).
  intros H. remember (gcd a b) as g. remember (gcd c d) as h. rewrite Ha, Hc.
  assert (n = m). {
    apply (coprime_equiv _ (b / h) _ (d / g)).
    - destruct b.
      + unfold frac_equiv in *. rewrite Nat.gcd_0_r, Nat.mul_0_r in *. subst.
    - admit.
    - admit.
      
  } lia.
 
Admitted.


Theorem frac_div (a b c d z: nat) :
  frac_equiv a b c d -> (z | c) -> (z | d) -> frac_equiv a b (c / z) (d / z).
Proof. 
  unfold frac_equiv. intros e nd dd. destruct z.
  - cbn. rewrite <- mult_n_O. auto.
  - rewrite (Nat.mul_comm _ b), <- Nat.divide_div_mul_exact, <- Nat.divide_div_mul_exact; auto.
    f_equal. lia.
Qed.

Theorem frac_equiv_same (p q p' q': nat) : q > 0 -> q' > 0 ->
  frac_equiv p q p' q' <-> frac_equiv' p q p' q'.
Proof.
  unfold frac_equiv, frac_equiv', normQ. intros qp g'p. split; intro H.
  - destruct p, p'; try lia. 
    + rewrite Nat.gcd_0_l, Nat.gcd_0_l, Nat.div_0_l, Nat.div_0_l, Nat.div_same, Nat.div_same; try lia.
      auto.
    + assert (CoPrime (S p / gcd (S p) q) (q / gcd (S p) q) /\
        frac_equiv (S p) q (S p / gcd (S p) q) (q / gcd (S p) q)) 
          by (apply frac_equiv_const_mul; lia).
      assert (CoPrime (S p' / gcd (S p') q') (q' / gcd (S p') q') /\
        frac_equiv (S p') q' (S p' / gcd (S p') q') (q' / gcd (S p') q')) 
          by (apply frac_equiv_const_mul; lia).
      destruct H0 as (c0 & e0). destruct H1 as (c1 & e1). rewrite pair_equal_spec.
      split.
      * apply (coprime_equiv _ (q / gcd (S p) q)  _ (q' / gcd (S p') q')); auto.
        apply (frac_equiv_trans _ _ (S p) q _ _); try apply frac_equiv_symm; auto.
        apply (frac_equiv_trans _ _ (S p') q' _ _); try apply frac_equiv_symm; auto.
      * apply (coprime_equiv _ (S p / gcd (S p) q)  _ (S p' / gcd (S p') q')); 
        try apply CoPrime_symm; auto.
        apply frac_equiv_symm'.
        apply (frac_equiv_trans _ _ (S p) q _ _); try apply frac_equiv_symm; auto.
        apply (frac_equiv_trans _ _ (S p') q' _ _); try apply frac_equiv_symm; auto.
  - inversion H. apply (frac_equiv_trans p q (p / gcd p q) (q / gcd p q) p' q').
    + apply frac_div.
      * unfold frac_equiv. auto.
      * apply Nat.gcd_divide.
      * apply Nat.gcd_divide.
    + rewrite H1, H2. apply frac_equiv_symm. apply frac_div.
      * unfold frac_equiv. auto.
      * apply Nat.gcd_divide.
      * apply Nat.gcd_divide.
Qed.

Theorem frac_exp (p q p' q': nat) :
  frac_equiv p q p' q' -> CoPrime p q -> exists k, p' = k * p /\ q' = k * q.
Proof.
  intros E co. destruct q, q'.
  - unfold frac_equiv, CoPrime in *. rewrite Nat.gcd_0_r in co. subst.
    exists p'. lia.
  - unfold frac_equiv, CoPrime in *. rewrite Nat.gcd_0_r in co. subst.
    rewrite Nat.mul_1_l, Nat.mul_0_r in E. inversion E.
  - unfold frac_equiv, CoPrime in *. exists 0. cbn. split; auto. Search (_ * _).
    admit.
  - exists (gcd p q).
Admitted.

Theorem qplus'_is_unique (p q p' q' n: nat) : 
  p > 0 -> q > 0 -> p' > 0 -> q' > 0 ->
  frac_equiv p q p' q' -> qplus' p q n = qplus' p' q' n.
Proof.
  unfold frac_equiv. intros pp pq pp' pq' eq.
  assert (CoPrime (p / gcd p q) (q / gcd p q) /\ frac_equiv p q (p / gcd p q) (q / gcd p q)).
  - apply frac_equiv_const_mul; auto.
  - destruct H as (c & f). transitivity (qplus' p'' q'' n).
    + assert (exists k, p = k * p'' /\ q = k * q'') by
      (apply frac_exp; auto; apply frac_equiv_symm; auto).
      destruct H as (k & e1 & e2). destruct k.
      * cbn in *. subst. exfalso. apply (Gt.gt_irrefl 0). auto. 
      * rewrite e1, e2. apply qplus'_mul_const.
    + assert (frac_equiv p' q' p'' q'') by
      (apply (frac_equiv_trans p' q' p q); auto; apply frac_equiv_symm; auto).
      assert (exists k, p' = k * p'' /\ q' = k * q'') by
      (apply frac_exp; auto; apply frac_equiv_symm; auto).
      destruct H0 as (k & e1 & e2). destruct k.
      * cbn in *. subst. exfalso. apply (Gt.gt_irrefl 0). auto. 
      * rewrite e1, e2. symmetry. apply qplus'_mul_const.
Qed.

Function normQ (q : Q) : Q :=
let (p, q) := q in
match p, q with
| S p', S q' => let gcd := euclid p' q' in (p / gcd, q / gcd)
| _   , _    => (O, O)
end.

Definition frac_equiv (a b : Q) : Prop :=
  normQ a = normQ b.

Theorem frac_equiv_for_qplus : forall p q p' q': nat,
  frac_equiv (S p, S q) (S p', S q') -> qplus p q = qplus p' q'.
Proof.
  unfold qplus, frac_equiv. intros p q p' q' H. cbn in *. inversion H.
  





