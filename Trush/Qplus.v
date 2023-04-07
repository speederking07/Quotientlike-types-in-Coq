Require Import Recdef.
Require Import Nat.
Require Import Lia.
Require Import PeanoNat.
Require Import Setoid.


Notation "( x | y )" := (Nat.divide x y) (at level 0).

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

Definition CoPrime (a b: nat) := gcd a b = 1.




(* Baisc math lemmas *)
Lemma CoPrime_symm (a b: nat) : CoPrime a b -> CoPrime b a.
Proof.
  unfold CoPrime. rewrite Nat.gcd_comm. auto.
Qed.

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

Lemma mul_div (a b : nat) : (b | a) -> a / b * b = a.
Proof.
  intros h. destruct h as (k & H). rewrite H. destruct b.
  - cbn. rewrite Nat.mul_0_r. auto.
  - rewrite Nat.div_mul; auto.
Qed.

Lemma div_sub_same (a b c: nat) : c <> 0 -> (a * c - b * c) / c = a - b.
Proof.
  intros H. rewrite <- (Nat.mul_cancel_r _ _ c); auto. rewrite mul_div.
  - rewrite Nat.mul_sub_distr_r. auto.
  - exists (a - b). rewrite Nat.mul_sub_distr_r. auto.
Qed.

Lemma div_add_same (a b c: nat) : c <> 0 -> (a * c + b * c) / c = a + b.
Proof.
  intros H. rewrite <- (Nat.mul_cancel_r _ _ c); auto. rewrite mul_div.
  - rewrite Nat.mul_add_distr_r. auto.
  - exists (a + b). rewrite Nat.mul_add_distr_r. auto.
Qed.

Lemma div_sub_add_same (a b c d: nat) : d <> 0 -> (a * d - b * d + c * d) / d = a - b + c.
Proof.
  intros H. rewrite <- (Nat.mul_cancel_r _ _ d); auto. rewrite mul_div.
  - rewrite Nat.mul_add_distr_r, Nat.mul_sub_distr_r. auto.
  - exists (a - b + c). rewrite Nat.mul_add_distr_r, Nat.mul_sub_distr_r. auto.
Qed.

Lemma mul_div_eq (a b c: nat) : c <> 0 -> a = b * c -> b = a / c.
Proof.
  intros P H.
  rewrite <-(Nat.mul_cancel_r _ _ c); auto. rewrite mul_div; auto. 
  exists b. auto.
Qed.

Lemma le_cancel_r (a b c: nat) : c <> 0 -> a * c <= b * c -> a <= b.
Proof.
  intros P H. destruct c; try contradiction. destruct (a ?= b) eqn:E.
  - rewrite Nat.compare_eq_iff in *. lia.
  - rewrite Nat.compare_lt_iff in *. lia.
  - assert (S c * a ?= S c * b = Gt) by (rewrite <- E; apply pos_mul_comp).
    rewrite Nat.mul_comm, (Nat.mul_comm b) in H.
    rewrite Nat.compare_gt_iff in *. lia.
Qed.

Lemma gcd_pos_l (p q: nat) : p > 0 -> gcd p q <> 0.
Proof.
  intros H E. rewrite Nat.gcd_eq_0 in E. lia.
Qed.

Lemma le_exists_sum (a b: nat) : a <= b -> exists c, b = a + c.
Proof.
  intros H. exists (b - a). lia.
Qed.

Lemma zero_div (x: nat) : x / 0 = 0.
Proof.
  induction x; auto.
Qed.

Lemma id_mul_is_1 (a b : nat) : a > 0 -> a = b * a -> b = 1.
Proof.
  intros P H. destruct a.
  - lia.
  - destruct b.
    + cbn in *. inversion H.
    + lia.
Qed.

Lemma lt_gt_symm (a b: nat) : a > b <-> b < a.
Proof.
  split; lia.
Qed.

Lemma eq_sym {A: Type} (x y: A) : x = y <-> y = x.
Proof.
  split; auto.
Qed.

Lemma gt_zero (x: nat) : x > 0 <-> x <> 0.
Proof.
  lia.
Qed.

Theorem co_prime_gcd (a b: nat) :
  a > 0 -> CoPrime (a / gcd a b) (b / gcd a b).
Proof.
  intros Pa. apply Nat.gcd_div_gcd; auto. destruct (gcd a b) eqn: H; try lia.
  assert (a = 0) by (apply (Nat.gcd_eq_0_l a b); auto). lia. 
Qed.

Lemma div_swap (a b c : nat) : b <> 0 -> (b | c) -> a * b = c -> a = c / b.
Proof.
  intros P (k & D) E. rewrite D in *. rewrite Nat.div_mul; auto.
  rewrite Nat.mul_cancel_r in E; auto.
Qed.

Lemma div_mul_comm (a b c: nat) : (b | a) -> (b | c) -> a / b * c = a * (c / b).
Proof.
  intros (k & H) (k' & H'). destruct b.
  - lia.
  - rewrite H, H'. rewrite Nat.div_mul, Nat.div_mul; lia.
Qed.




(* Fuel lemmas *)
Function len (x: Qplus) : nat :=
match x with
| One  => 1
| N x' => S (len x')
| D x' => S (len x')
end.

Lemma more_than_enough_fuel (p q n: nat) : len (qplus_c' p q n) < n -> 
  qplus_c' p q n = qplus_c' p q (S n).
Proof.
  revert p q. induction n; intros p q H.
  - lia. 
  - cbn in *. destruct (p ?= q) eqn:E; auto;
    cbn in *; f_equal; apply IHn; apply Lt.lt_S_n; auto.
Qed.

Lemma enough_fuel (p q h: nat) : p > 0 -> q > 0 -> 
  (p + q) / gcd p q <= h -> len (qplus_c' p q h) < h.
Proof.
  revert p q. induction h; intros p q Pp Pq E;
  assert (G: gcd p q <> 0) by (apply gcd_pos_l; auto);
  assert (gcd p q | p) by apply Nat.gcd_divide; destruct H as (k & P);
  assert (gcd p q | q) by apply Nat.gcd_divide; destruct H as (k' & Q).
  - remember (gcd p q) as g. rewrite P, Q, div_add_same in E; try lia.
    destruct k, k'; try lia.  
  - cbn. destruct (p ?= q) eqn:F.
    + cbn in *. rewrite Nat.compare_eq_iff in F. subst.
      assert ((q + q) / q = (q + 1 * q) / q) by (rewrite Nat.mul_1_l; auto).
      rewrite Nat.gcd_diag, H, Nat.div_add, Nat.div_same in E; lia.
    + cbn. apply Lt.lt_n_S. rewrite Nat.compare_lt_iff in F. apply IHh; try lia.
      rewrite Nat.gcd_sub_diag_r; try lia. apply Le.le_S_n. 
      apply (Nat.le_trans _ ((p + q) / gcd p q) _); auto.
      remember (gcd p q) as g. rewrite P, Q. 
      rewrite Nat.div_add_l, div_add_same, div_sub_same; try lia.
      rewrite Minus.le_plus_minus_r; try lia.
      rewrite (mul_div_eq p k g); try lia. rewrite (mul_div_eq q k' g); try lia.
      apply (le_cancel_r _ _ g); auto. rewrite mul_div, mul_div; 
      try lia; subst; apply Nat.gcd_divide.
    + cbn. apply Lt.lt_n_S. rewrite Nat.compare_gt_iff in F. apply IHh; try lia.
      rewrite Nat.gcd_comm, Nat.gcd_sub_diag_r, Nat.gcd_comm; try lia. 
      apply Le.le_S_n. apply (Nat.le_trans _ ((p + q) / gcd p q) _); auto.
      remember (gcd p q) as g. rewrite P, Q.
      rewrite div_sub_add_same, div_add_same; lia.
Qed.

Lemma fuel_for_qplus_c (p q: nat) : p > 0 -> q > 0 -> 
  qplus_c' p q ((p + q) / gcd p q) = qplus_c' p q (S ((p + q) / gcd p q)).
Proof.
  intros Pp Pq. apply more_than_enough_fuel. apply enough_fuel; lia.
Qed.

Lemma fuel_for_qplus_c_add (p q f: nat) : p > 0 -> q > 0 -> 
  qplus_c' p q ((p + q) / gcd p q) = qplus_c' p q (f + (p + q) / gcd p q).
Proof.
  intros Pp Pq. induction f; auto. rewrite Nat.add_succ_l.
  rewrite <- more_than_enough_fuel; auto. destruct IHf. induction f.
  - cbn. apply enough_fuel; auto.
  - lia.
Qed. 

Lemma fuel_for_qplus_c' (p q f: nat) : p > 0 -> q > 0 -> 
  ((p + q) / gcd p q) <= f -> qplus_c' p q ((p + q) / gcd p q) = qplus_c' p q f.
Proof.
  intros Pp Pq H. 
  assert (exists k, f = ((p + q) / gcd p q) + k) by (apply le_exists_sum; auto).
  destruct H0 as (k & E). rewrite (Nat.add_comm _ k) in E. rewrite E.
  apply fuel_for_qplus_c_add; auto.
Qed.






(* Valid definition and lemmas *)
Definition valid (x: Q) := num x > 0 /\ den x > 0.

Lemma qplus_valid (x: Qplus) : valid (qplus_i x).
Proof.
  unfold valid. induction x; auto.
  - cbn. destruct (qplus_i x). cbn in *. lia.
  - cbn. destruct (qplus_i x). cbn in *. lia.
Qed.

Lemma reduces_valid (p q: nat) : valid (p, q) -> 
  valid (p / gcd p q, q / gcd p q).
Proof.
  intros (Pp & Pq). assert (gcd p q <> 0).
  { cbn in *. intros H. rewrite Nat.gcd_eq_0 in H. lia. }
  split; cbn in *; rewrite gt_zero; intros H'; 
  rewrite <- (Nat.mul_cancel_r _ _ (gcd p q)) in H'; auto;
  rewrite mul_div in H'; try lia. 
  - apply Nat.gcd_divide_l.
  - apply Nat.gcd_divide_r.
Qed.

Lemma valid_sub_l (a b c: nat) : a > b -> valid (a, b) -> valid (a - b, b).
Proof.
  unfold valid. cbn. intros E (Pa & Pb). split; lia.
Qed.

Lemma valid_sub_r (a b c: nat) : b > a -> valid (a, b) -> valid (a , b - a).
Proof.
  unfold valid. cbn. intros E (Pa & Pb). split; lia.
Qed.





(* Multiplying by constant do not change trance *)
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
  - cbn. destruct (qplus_i x) eqn: e. 
    assert (num (qplus_i x) > 0 /\ den (qplus_i x) > 0) by apply qplus_valid.
    rewrite e in H. cbn in H. inversion H.  rewrite fuel_for_qplus_c; try lia. cbn.
    assert (n + n0 ?= n0 = Gt).
    + rewrite Nat.compare_gt_iff. lia.
    + rewrite H2, <- IHx. rewrite Nat.add_sub. f_equal. symmetry. 
      apply fuel_for_qplus_c'; auto. apply gcd_ge.
  - cbn. destruct (qplus_i x) eqn: e. 
    assert (num (qplus_i x) > 0 /\ den (qplus_i x) > 0) by apply qplus_valid.
    rewrite e in H. cbn in H. inversion H. 
    rewrite fuel_for_qplus_c; try lia. cbn. assert (n ?= n + n0 = Lt).
    + rewrite Nat.compare_lt_iff. lia.
    + rewrite H2, <- IHx. rewrite (Nat.add_comm n n0), Nat.add_sub. f_equal.
      symmetry. rewrite (Nat.add_comm n0 n), Nat.add_assoc. apply fuel_for_qplus_c'; auto.
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





(* Frac_eq definition and theorems *)
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

Theorem frac_eq_trans (x y z: Q) : valid x -> valid y -> valid z -> 
  frac_eq x y -> frac_eq y z -> frac_eq x z.
Proof.
  destruct x as (x & x'). destruct y as (y & y'). destruct z as (z & z').
  unfold valid, frac_eq. cbn. intros (Px & Px') (Py & Py') (Pz & Pz') H H'.
  assert (x * gcd y y' = y * gcd x x') by (apply gcd_equiv; auto).
  assert (P: gcd y y' <> 0) by (apply gcd_pos_l; auto).
  assert (E: x = y * gcd x x' / gcd y y'). 
  { apply div_swap; auto. apply Nat.divide_mul_l. apply Nat.gcd_divide. } 
  rewrite E in H. rewrite div_mul_comm, <- Nat.mul_assoc, Nat.mul_cancel_l in H; 
  try apply Nat.gcd_divide; try lia.
  - remember (gcd x x') as gx. remember (gcd y y') as gy. rewrite <-H, E.
    rewrite (Nat.mul_comm _ z'), <-(Nat.mul_cancel_r _ _ gy); try lia.
    rewrite <- Nat.mul_assoc, <- Nat.mul_assoc, Heqgx, Heqgy. 
    rewrite mul_div, <- Nat.divide_div_mul_exact, mul_div; 
    try apply Nat.gcd_divide; try lia.
    + rewrite Nat.mul_assoc, (Nat.mul_comm z'), H'. lia.
    + apply Nat.divide_mul_r. apply Nat.gcd_divide.
    + apply Nat.divide_mul_l. apply Nat.gcd_divide.
  - apply Nat.divide_mul_l. apply Nat.gcd_divide.  
Qed.






(* Proof that qplus glues equivalet fractions *)
Theorem qplus_glue_frac_eq (x y: Q) : valid x -> valid y ->
  frac_eq x y -> qplus_c x = qplus_c y.
Proof.
  destruct x as (x & x'). destruct y as (y & y'). intros Vx Vy H.
  assert (frac_eq (x, x') (x / gcd x x', x' / gcd x x')).
  { unfold frac_eq in *. cbn in *. apply frac_div; try apply Nat.gcd_divide; auto. }
  assert (frac_eq (y, y') (y / gcd y y', y' / gcd y y')).
  { unfold frac_eq in *. cbn in *. apply frac_div; try apply Nat.gcd_divide; auto. }
  assert (frac_eq (x / gcd x x', x' / gcd x x') (y / gcd y y', y' / gcd y y')).
  { apply (frac_eq_trans _ (x, x')); try apply reduces_valid; auto.
    - apply frac_eq_symm; auto.
    - apply (frac_eq_trans _ (y, y')); try apply reduces_valid; auto.
  }
  transitivity (qplus_c (x / gcd x x', x' / gcd x x')); cycle 1.
  transitivity (qplus_c (y / gcd y y', y' / gcd y y')); cycle 2.
  - f_equal. f_equal.
    + apply (coprime_equiv _ (x' / gcd x x') _ (y' / gcd y y')); try apply co_prime_gcd; auto;
      unfold valid in *; cbn in *; destruct Vx, Vy; auto.
    + unfold valid in *; cbn in *; destruct Vx, Vy.
      apply (coprime_equiv _ (x / gcd x x')  _ (y / gcd y y')).
      1-2: rewrite Nat.gcd_comm; apply co_prime_gcd; auto.
      unfold frac_eq in H2. cbn in *. lia.
  - symmetry. transitivity (qplus_c (gcd y y' * (y / gcd y y'), gcd y y' * (y' / gcd y y'))).
    + rewrite Nat.mul_comm, (Nat.mul_comm (gcd y y')), mul_div, mul_div; 
      auto; apply Nat.gcd_divide.
    + remember (gcd y y') as g. destruct g.
      * rewrite zero_div, zero_div. auto.
      * apply qplus_c_mul_pos.
  - transitivity (qplus_c (gcd x x' * (x / gcd x x'), gcd x x' * (x' / gcd x x'))).
    + rewrite Nat.mul_comm, (Nat.mul_comm (gcd x x')), mul_div, mul_div;
      auto; apply Nat.gcd_divide.
    + remember (gcd x x') as g. destruct g.
      * rewrite zero_div, zero_div. auto.
      * apply qplus_c_mul_pos.
Qed.




(* Ancilary lemmas about reverting gplus_c *)
Lemma qplus_0_l (a : nat) : qplus_c (O, S a) = D One.
Proof.
  unfold qplus_c. rewrite Nat.gcd_0_l, Nat.add_0_l, Nat.div_same; try lia; auto.
Qed.

Lemma qplus_0_r (a : nat) : qplus_c (S a, O) = N One.
Proof.
  unfold qplus_c. rewrite Nat.gcd_0_r, Nat.add_0_r, Nat.div_same; try lia; auto.
Qed.

Lemma qplus_go_back_One (p q: nat) : qplus_c (p, q) = One <->
  p = q.
Proof.
  split.
  - intro H. destruct p, q; auto.
    + rewrite qplus_0_l in H. inversion H.
    + rewrite qplus_0_r in H. inversion H.
    + unfold qplus_c in *. rewrite fuel_for_qplus_c in H; try lia. cbn in *. 
      destruct (p ?= q) eqn:e; try inversion H. 
      rewrite Nat.compare_eq_iff in e. auto.
  - intros. subst. cbn. rewrite Nat.gcd_diag. destruct q; auto.
    assert ((S q + S q) / S q = 2).
    { rewrite <- (Nat.mul_cancel_r _ _ (S q)); try lia. rewrite mul_div; try lia.
      exists 2. lia. }
    rewrite H. cbn. rewrite Nat.compare_refl. auto.
Qed.

Lemma qplus_N_bigger (p q: nat) (t: Qplus) :
  qplus_c (p, q) = N t -> p > q.
Proof.
  intros H. destruct p, q; auto. 
  - inversion H.
  - rewrite qplus_0_l in H. inversion H.
  - lia.
  - unfold qplus_c in *. rewrite fuel_for_qplus_c in *; try lia. cbn in *.
    destruct (p ?= q) eqn:e; inversion H.
    apply Compare_dec.nat_compare_Gt_gt. assumption.
Qed.

Lemma qplus_D_bigger (p q: nat) (t: Qplus) :
  qplus_c (p, q) = D t -> q > p.
Proof.
  intros H. destruct p, q; auto. 
  - inversion H.
  - lia.
  - rewrite qplus_0_r in H. inversion H.
  - unfold qplus_c in *. rewrite fuel_for_qplus_c in *; try lia. cbn in *.
    destruct (p ?= q) eqn:e; inversion H.
    apply Compare_dec.nat_compare_Lt_lt. assumption.
Qed.

Lemma qplus_go_back_N (p q: nat) (t: Qplus) : valid (p, q) -> 
  qplus_c (p, q) = N t -> qplus_c (p - q, q) = t.
Proof.
  intros  (Vp & Vq). cbn in *.
  intros H. assert (p > q) by (apply (qplus_N_bigger _ _ t); auto). 
  rewrite fuel_for_qplus_c in H; auto. cbn in *.
  rewrite Compare_dec.nat_compare_gt in H0. rewrite H0 in H.
  rewrite <- Compare_dec.nat_compare_gt in H0.
  inversion H. apply fuel_for_qplus_c'; try lia.
  rewrite Nat.gcd_comm, Nat.gcd_sub_diag_r, Nat.gcd_comm; try lia.
  apply Nat.div_le_mono; try lia. intro G. rewrite Nat.gcd_eq_0 in G.
  lia.
Qed.

Lemma qplus_go_back_D (p q: nat) (t: Qplus) :  valid (p, q) ->  
  qplus_c (p, q) = D t -> qplus_c (p, q - p) = t.
Proof.
  intros  (Vp & Vq). cbn in *.
  intros H. assert (q > p) by (apply (qplus_D_bigger _ _ t); auto). 
  rewrite fuel_for_qplus_c in H; auto. cbn in *.
  Search (_ < _ <-> _ > _).
  rewrite lt_gt_symm, Compare_dec.nat_compare_lt in H0. rewrite H0 in H.
  rewrite <- Compare_dec.nat_compare_lt in H0.
  inversion H. apply fuel_for_qplus_c'; try lia.
  rewrite Nat.gcd_sub_diag_r, Nat.gcd_comm; try lia.
  apply Nat.div_le_mono; try lia. intro G. rewrite Nat.gcd_eq_0 in G.
  lia.
Qed.

Lemma frac_eq_N (p q p' q': nat) : p > q -> p' > q' ->
  frac_eq (p - q, q) (p' - q', q') -> frac_eq (p, q) (p', q').
Proof.
  unfold frac_eq. cbn. intros P P' H. 
  rewrite Nat.mul_sub_distr_r, Nat.mul_sub_distr_r, (Nat.mul_comm q q') in H. 
  rewrite <- (Nat.add_cancel_r _ _ (q' * q)), Nat.sub_add, Nat.sub_add in H; auto.
  - apply Nat.mul_le_mono; lia.
  - rewrite (Nat.mul_comm p q'). apply Nat.mul_le_mono; lia.
Qed.

Lemma frac_eq_D (p q p' q': nat) : q > p -> q' > p' ->
  frac_eq (p, q - p) (p', q' - p') -> frac_eq (p, q) (p', q').
Proof.
  unfold frac_eq. cbn. intros P P' H. 
  rewrite Nat.mul_sub_distr_l, Nat.mul_sub_distr_l, (Nat.mul_comm p p') in H. 
  rewrite <- (Nat.add_cancel_r _ _ (p' * p)), Nat.sub_add, Nat.sub_add in H; auto.
  - apply Nat.mul_le_mono; lia.
  - rewrite (Nat.mul_comm p q'). apply Nat.mul_le_mono; lia.
Qed.






(* qplus is valid representation for fractions *)
Theorem qplus_epi (x y: Q) : valid x -> valid y ->
  qplus_c x = qplus_c y -> frac_eq x y.
Proof.
  destruct x as (x, x'). destruct y as (y, y'). revert y y'. 
  remember (qplus_c (x, x')) as t. revert Heqt. revert x x'. 
  induction t; intros x x' E y y' Vx Vy H.
  - rewrite eq_sym, qplus_go_back_One in E, H. subst. unfold frac_eq.
    cbn. lia.
  - assert (x > x') by (apply (qplus_N_bigger _ _ t); auto). 
    assert (y > y') by (apply (qplus_N_bigger _ _ t); auto).
    assert (t = qplus_c (x - x', x')) by (symmetry; apply qplus_go_back_N; auto).
    assert (t = qplus_c (y - y', y')) by (symmetry; apply qplus_go_back_N; auto).
    apply frac_eq_N; auto. apply IHt; auto; apply valid_sub_l; auto.
  - assert (x' > x) by (apply (qplus_D_bigger _ _ t); auto). 
    assert (y' > y) by (apply (qplus_D_bigger _ _ t); auto).
    assert (t = qplus_c (x, x' - x)) by (symmetry; apply qplus_go_back_D; auto).
    assert (t = qplus_c (y, y' - y)) by (symmetry; apply qplus_go_back_D; auto).
    apply frac_eq_D; auto. apply IHt; auto; apply valid_sub_r; auto.
Qed.

Theorem qplus_mono' : forall y: Qplus, exists x: Q, qplus_c x = y.
Proof.
  intros y. exists (qplus_i y). apply qplus_mono.
Qed. 




Inductive FullQ :=
| Pos  : Qplus -> FullQ
| Zero : FullQ
| Neg  : Qplus -> FullQ.

