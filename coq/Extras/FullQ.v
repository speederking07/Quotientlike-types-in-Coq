Require Import Lia.
Require Import Coq.Program.Equality.

Require Import Qplus.
Require Import Integer.


Inductive FullQ :=
| QPos  : Qplus -> FullQ
| QZero : FullQ
| QNeg  : Qplus -> FullQ.

Definition Q' : Type := Z * Z.





(* Fraction equality equvalance relation and proof *)
Inductive frac_eq' : Q' -> Q' -> Prop :=
| PosFracEq  : forall (n d n' d' : nat), frac_eq (S n, S d) (S n', S d') -> 
               frac_eq' (Pos n, Pos d) (Pos n', Pos d')
| ZeroFracEq : forall (d d' : nat), frac_eq' (Zero, Pos d) (Zero, Pos d')
| NegFracEq  : forall (n d n' d' : nat), frac_eq (S n, S d) (S n', S d') -> 
               frac_eq' (Neg n, Pos d) (Neg n', Pos d').

Inductive QValid : Q' -> Prop :=
| V : forall (n: Z) (d: nat), QValid (n, Pos d).

Theorem frac_eq'_valid (x y: Q') : frac_eq' x y -> QValid x /\ QValid y.
Proof.
  intros H. destruct x as [n d]. destruct y as [n' d'].
  destruct d, d'; dependent destruction H; split; constructor.
Qed.

Theorem frac_eq'_refl (x: Q') `{V: QValid x} : frac_eq' x x.
Proof.
  dependent destruction V. destruct n.
  - constructor. apply frac_eq_relf. unfold valid. cbn. lia.
  - constructor.
  - constructor. apply frac_eq_relf. unfold valid. cbn. lia.
Qed.

Theorem frac_eq'_sym (x y: Q') : frac_eq' x y -> frac_eq' y x.
Proof.
  intros H. assert (Vx: QValid x) by now apply (frac_eq'_valid x y).
  assert (Vy: QValid y) by now apply (frac_eq'_valid x y).
  dependent destruction Vx. dependent destruction Vy. 
  destruct n, n0; dependent destruction H. 
  - constructor. now apply frac_eq_symm.
  - constructor.
  - constructor. now apply frac_eq_symm.
Qed.

Theorem frac_eq'_trans (x y z: Q') : frac_eq' x y -> frac_eq' y z -> frac_eq' x z.
Proof.
  intros H H'. assert (Vx: QValid x) by now apply (frac_eq'_valid x y).
  assert (Vy: QValid y) by now apply (frac_eq'_valid x y).
  assert (Vz: QValid z) by now apply (frac_eq'_valid y z).
  dependent destruction Vx. dependent destruction Vy. dependent destruction Vz. 
  destruct n, n0, n1; dependent destruction H; dependent destruction H'. 
  - constructor. apply frac_eq_trans with (y := (S n0, S d0)); [.. | auto | auto].
    1-3: unfold valid; cbn; lia.
  - constructor.
  - constructor. apply frac_eq_trans with (y := (S n0, S d0)); [.. | auto | auto].
    1-3: unfold valid; cbn; lia.
Qed.

Theorem frac_eq'_equal (n n' d d': Z) : QValid (n, d) -> n = n' -> d = d' -> 
  frac_eq' (n, d) (n', d').
Proof.
  intros V [] []. now apply frac_eq'_refl.
Qed.

Theorem frac_eq'_def (n n' d d': Z) `{Vx: QValid (n, d)} `{Vy: QValid (n', d')}: 
  n * d' = n' * d <-> frac_eq' (n, d) (n', d').
Proof.
  split.
  - intros H. dependent destruction Vx. dependent destruction Vy. destruct n, n'.
    + constructor. rewrite pos_mul, pos_mul in H. inversion H. unfold frac_eq.
      cbn. lia.
    + rewrite pos_mul in H. inversion H.
    + rewrite pos_mul, neg_pos_mul in H. inversion H.
    + rewrite pos_mul in H. inversion H.
    + constructor.
    + rewrite neg_pos_mul in H. inversion H.
    + rewrite pos_mul, neg_pos_mul in H. inversion H.
    + rewrite  neg_pos_mul in H. inversion H.
    + constructor. rewrite neg_pos_mul, neg_pos_mul in H. unfold frac_eq.
      cbn. inversion H. lia.
  - intros H. dependent destruction H; unfold frac_eq in *; cbn [num den] in *.
    + rewrite pos_mul, pos_mul. f_equal. lia.
    + auto.
    + rewrite neg_pos_mul, neg_pos_mul. f_equal. lia.
Qed.





(* FullQ and Q' transport functions *) 
Definition fullQ_c (q: Q') : FullQ :=
match q with
| (Pos n, d) => QPos (qplus_c (S n, abs' d))
| (Zero , d) => QZero
| (Neg n, d) => QNeg (qplus_c (S n, abs' d))
end.

Definition toPos (x: nat) : Z :=
match x with
| O   => Zero
| S n => Pos n
end.

Definition fullQ_i (q: FullQ) : Q' :=
match q with
| QPos q' => let (n, d) := qplus_i q' in (toPos n, toPos d)
| QZero   => (Zero, Pos O)
| QNeg q' => let (n, d) := qplus_i q' in (-toPos n, toPos d)
end.


(* Q' and FullQ izomorphism theorems *)
Theorem fullQ_i_is_valid (q: FullQ) : QValid (fullQ_i q).
Proof.
  destruct q; cbn; [|constructor|]; assert (valid (qplus_i q)) by apply qplus_valid;
  destruct H as [_ dp]; unfold den in *; destruct (qplus_i q); destruct n0; 
  cbn; [lia | constructor | lia | constructor].
Qed.

Lemma abs_toPos (d: nat) : abs' (toPos d) = d.
Proof.
  induction d; auto.
Qed.

Lemma fullQ_mono_pos (n d: nat) (q: Qplus) : 
  qplus_i q = (n, d) -> fullQ_c (toPos n, toPos d) = QPos q.
Proof.
  intros H. assert (valid (qplus_i q)) by apply qplus_valid. destruct H0 as [dn dp].
  rewrite H in *. cbn [num den] in *. destruct n; [lia|].
  cbn [toPos fullQ_c]. now rewrite abs_toPos, <-H, qplus_mono.
Qed.

Lemma fullQ_mono_neg (n d: nat) (q: Qplus) : 
  qplus_i q = (n, d) -> fullQ_c (- toPos n, toPos d) = QNeg q.
Proof.
  intros H. assert (valid (qplus_i q)) by apply qplus_valid. destruct H0 as [dn dp].
  rewrite H in *. cbn [num den] in *. destruct n; [lia|].
  cbn [toPos neg fullQ_c]. now rewrite abs_toPos, <-H, qplus_mono.
Qed.

Theorem fullQ_mono (q: FullQ) : fullQ_c (fullQ_i q) = q.
Proof.
  destruct q; [| auto |]; cbn in *; destruct (qplus_i q) as [n d] eqn:p.
  - now apply fullQ_mono_pos. 
  - now apply fullQ_mono_neg.
Qed.

Theorem fullQ_glue_frac_eq' (x y: Q') `{Vx: QValid x} `{Vy: QValid y} :
  frac_eq' x y -> fullQ_c x = fullQ_c y.
Proof.
  dependent destruction Vx. dependent destruction Vy. intros H.
  destruct n, n0; dependent destruction H; [| auto |].
  - cbn [fullQ_c]. f_equal. apply qplus_glue_frac_eq; [..| auto].
    1-2: unfold valid; cbn; lia.
  - cbn [fullQ_c]. f_equal. apply qplus_glue_frac_eq; [..| auto].
    1-2: unfold valid; cbn; lia.
Qed.

Theorem fullQ_epi (x y: Q') `{Vx: QValid x} `{Vy: QValid y} :
  fullQ_c x = fullQ_c y -> frac_eq' x y.
Proof.
  dependent destruction Vx. dependent destruction Vy. intros H.
  destruct n, n0. 
  2-4,6-8: inversion H.
  - cbn [fullQ_c abs'] in H. 
    assert (H' : qplus_c (S n, S d) = qplus_c (S n0,S d0)) by now inversion H.
    constructor. apply qplus_epi; (unfold valid; cbn; lia || auto).
  - constructor.
  - cbn [fullQ_c abs'] in H. 
    assert (H' : qplus_c (S n, S d) = qplus_c (S n0,S d0)) by now inversion H.
    constructor. apply qplus_epi; (unfold valid; cbn; lia || auto).
Qed.

Theorem fullQ_epi' (x: Q') `{Vx: QValid x} : frac_eq' x (fullQ_i (fullQ_c x)).
Proof.
  apply fullQ_epi; [auto | apply fullQ_i_is_valid | now rewrite fullQ_mono].
Qed.



(* Basic operations definitions *)
Definition Qinv (q: FullQ) : FullQ :=
match q with
| QPos x => QPos (Qplus_inv x)
| QZero  => QZero
| QNeg x => QNeg (Qplus_inv x)
end.

Definition Qneg (q: FullQ) : FullQ :=
match q with
| QPos x => QNeg x
| QZero  => QZero
| QNeg x => QPos x
end.

Definition Qadd' (x y: Q') : Q' :=
match x, y with
| (n, d), (n', d') => (d' * n + d * n', d * d')
end.

Definition Qadd (x y: FullQ) : FullQ :=
match (fullQ_i x), (fullQ_i y) with
| x', y' => fullQ_c (Qadd' x' y')
end.

Definition Qmul' (x y: Q') : Q' :=
match x, y with
| (n, d), (n', d') => (n * n', d * d')
end.

Definition Qmul (x y: FullQ) : FullQ :=
match (fullQ_i x), (fullQ_i y) with
| x', y' => fullQ_c (Qmul' x' y')
end.



Declare Scope Q_scope.
Delimit Scope Q_scope with FullQ.
Bind Scope Q_scope with FullQ.
Open Scope Q_scope.

Notation "- x" := (Qneg x) : Q_scope.
Infix "+" := Qadd : Q_scope.
Infix "*" := Qmul : Q_scope.


(* FullQ add properties proofs *)
Theorem Qadd_neg_r (x: FullQ) : x + (-x) = QZero.
Proof.
  destruct x; cbn; [| auto |].
  - unfold Qadd, Qadd'. cbn [fullQ_i]. destruct (qplus_i q). 
    now rewrite mul_r_neg, add_neg_r.
  - unfold Qadd, Qadd'. cbn [fullQ_i]. destruct (qplus_i q). 
    now rewrite mul_r_neg, add_neg_l.
Qed.

Theorem Qadd_zero_r (x: FullQ) : x + QZero = x.
Proof.
  destruct x; cbn; [| auto |].
  - unfold Qadd, Qadd'. cbn [fullQ_i]. destruct (qplus_i q) as [n d] eqn:p.
    rewrite mul_r_zero, add_r_zero, mul_r_one, mul_comm, mul_r_one.
    now apply fullQ_mono_pos.
  - unfold Qadd, Qadd'. cbn [fullQ_i]. destruct (qplus_i q) as [n d] eqn:p.
    rewrite mul_r_zero, add_r_zero, mul_r_one, mul_comm, mul_r_one.
    now apply fullQ_mono_neg.
Qed.

Theorem Qadd'_comm (x y: Q') : Qadd' x y = Qadd' y x.
Proof.
  unfold Qadd'. destruct x as [n d]. destruct y as [n' d']. f_equal.
  - apply add_comm.
  - apply mul_comm.
Qed.

Theorem Qadd_comm (x y: FullQ) : x + y = y + x.
Proof.
  unfold Qadd. now rewrite Qadd'_comm.
Qed.

Theorem Qadd_neg_l (x: FullQ) : (-x) + x = QZero.
Proof.
  now rewrite Qadd_comm, Qadd_neg_r.
Qed.

Theorem Qadd_zero_l (x: FullQ) : QZero + x = x.
Proof.
  now rewrite Qadd_comm, Qadd_zero_r.
Qed.

Lemma Qadd'_frac_eq_l (x y z: Q') `{Vx: QValid x} : 
  frac_eq' y z -> frac_eq' (Qadd' x y) (Qadd' x z).
Proof.
  intros H. unfold Qadd'.
  assert (Vy: QValid y) by now apply (frac_eq'_valid y z).
  assert (Vz: QValid z) by now apply (frac_eq'_valid y z).
  destruct x as [xn xd]. destruct y as [yn yd]. destruct z as [zn zd].
  apply frac_eq'_def.
  - dependent destruction Vx. dependent destruction Vy. rewrite pos_mul. constructor.
  - dependent destruction Vx. dependent destruction Vz. rewrite pos_mul. constructor.
  - rewrite mul_r_dist, mul_r_dist. rewrite <- frac_eq'_def in H; auto. f_equal.
    + rewrite (mul_comm _ xn), (mul_comm _ xn), mul_assoc, mul_assoc. f_equal.
      now rewrite (mul_comm xd), (mul_comm xd), <-mul_assoc, <-mul_assoc, (mul_comm yd). 
    + rewrite mul_assoc, mul_assoc. f_equal. 
      now rewrite (mul_comm xd), (mul_comm xd), <-mul_assoc, H, mul_assoc.
Qed.

Lemma Qadd'_frac_eq_r (x y z: Q') `{Vz: QValid z} : 
  frac_eq' x y -> frac_eq' (Qadd' x z) (Qadd' y z).
Proof.
  intros H.
  assert (Vx: QValid x) by now apply (frac_eq'_valid x y).
  assert (Vy: QValid y) by now apply (frac_eq'_valid x y).
  rewrite (Qadd'_comm x), (Qadd'_comm y). now apply Qadd'_frac_eq_l.
Qed.

Lemma Qadd'_valid (x y: Q') : QValid x -> QValid y -> QValid (Qadd' x y).
Proof.
  intros Vx Vy. dependent destruction Vx. dependent destruction Vy.
  cbn [Qadd']. rewrite pos_mul. constructor.
Qed.

Theorem Qadd'_assoc (x y z: Q') : Qadd' (Qadd' x y) z = Qadd' x (Qadd' y z).
Proof.
  destruct x as [xn xd]. destruct y as [yn yd]. destruct z as [zn zd].
  cbn [Qadd']. f_equal.
  - rewrite mul_l_dist, mul_l_dist, add_assoc. f_equal.
    + now rewrite <- mul_assoc, (mul_comm zd).
    + f_equal.
      * now rewrite <- mul_assoc, <- mul_assoc, (mul_comm zd).
      * apply mul_assoc.
  - apply mul_assoc.
Qed.

Theorem Qadd_assoc (x y z: FullQ) : (x + y) + z = x + (y + z).
Proof.
  unfold Qadd.
  assert (Vx: QValid (fullQ_i x)) by apply fullQ_i_is_valid.
  assert (Vy: QValid (fullQ_i y)) by apply fullQ_i_is_valid.
  assert (Vz: QValid (fullQ_i z)) by apply fullQ_i_is_valid.
  apply fullQ_glue_frac_eq'.
  - apply Qadd'_valid; [|auto]. apply fullQ_i_is_valid.
  - apply Qadd'_valid; [auto|]. apply fullQ_i_is_valid.
  - apply (frac_eq'_trans _ (Qadd' (Qadd' (fullQ_i x) (fullQ_i y)) (fullQ_i z))).
    2: apply (frac_eq'_trans _ (Qadd' (fullQ_i x) (Qadd' (fullQ_i y) (fullQ_i z)))).
    + apply Qadd'_frac_eq_r; [auto|]. apply frac_eq'_sym. apply fullQ_epi'. 
      now apply Qadd'_valid.
    + rewrite Qadd'_assoc. apply frac_eq'_refl. apply Qadd'_valid; [auto |].
      now apply Qadd'_valid.
    + apply Qadd'_frac_eq_l; [auto|]. apply fullQ_epi'. now apply Qadd'_valid.
Qed.



(* FullQ mul properties proofs *)
Theorem Qmul'_comm (x y: Q') : (Qmul' x y) = (Qmul' y x).
Proof.
  destruct x as [xn xd]. destruct y as [yn yd]. cbn [Qmul']. f_equal.
  - apply mul_comm.
  - apply mul_comm.
Qed.

Theorem Qmul'_assoc (x y z: Q') : Qmul' (Qmul' x y) z = Qmul' x (Qmul' y z).
Proof.
  destruct x as [xn xd]. destruct y as [yn yd]. destruct z as [zn zd].
  cbn [Qmul']. f_equal.
  - apply mul_assoc.
  - apply mul_assoc.
Qed.

Lemma Qmul'_valid (x y: Q') : QValid x -> QValid y -> QValid (Qmul' x y).
Proof.
  intros Vx Vy. dependent destruction Vx. dependent destruction Vy.
  cbn [Qmul']. rewrite pos_mul. constructor.
Qed.

Theorem Qmul_comm (x y: FullQ) : x * y = y * x.
Proof.
  unfold Qmul. now rewrite Qmul'_comm.
Qed.

Lemma Qmul'_frac_eq_l (x y z: Q') `{Vx: QValid x} : 
  frac_eq' y z -> frac_eq' (Qmul' x y) (Qmul' x z).
Proof.
  intros H. unfold Qmul'.
  assert (Vy: QValid y) by now apply (frac_eq'_valid y z).
  assert (Vz: QValid z) by now apply (frac_eq'_valid y z).
  destruct x as [xn xd]. destruct y as [yn yd]. destruct z as [zn zd].
  apply frac_eq'_def.
  - dependent destruction Vx. dependent destruction Vy. rewrite pos_mul. constructor.
  - dependent destruction Vx. dependent destruction Vz. rewrite pos_mul. constructor.
  - rewrite mul_assoc, mul_assoc. f_equal. rewrite (mul_comm xd), (mul_comm xd),
    <- mul_assoc, <- mul_assoc. f_equal. dependent destruction H.
    + rewrite pos_mul, pos_mul. unfold frac_eq in *. cbn in *. f_equal. lia.
    + auto.
    + rewrite neg_pos_mul, neg_pos_mul. unfold frac_eq in *. cbn in *. f_equal. lia.
Qed.

Lemma Qmul'_frac_eq_r (x y z: Q') `{Vz: QValid z} : 
  frac_eq' x y -> frac_eq' (Qmul' x z) (Qmul' y z).
Proof.
  intros H.
  assert (Vx: QValid x) by now apply (frac_eq'_valid x y).
  assert (Vy: QValid y) by now apply (frac_eq'_valid x y).
  rewrite (Qmul'_comm x), (Qmul'_comm y). now apply Qmul'_frac_eq_l.
Qed.

Theorem Qmul_assoc (x y z: FullQ) : (x * y) * z = x * (y * z).
Proof.
  assert (Vx: QValid (fullQ_i x)) by apply fullQ_i_is_valid.
  assert (Vy: QValid (fullQ_i y)) by apply fullQ_i_is_valid.
  assert (Vz: QValid (fullQ_i z)) by apply fullQ_i_is_valid.
  apply fullQ_glue_frac_eq'; unfold Qmul.
  - apply Qmul'_valid; [|auto]. apply fullQ_i_is_valid.
  - apply Qmul'_valid; [auto|]. apply fullQ_i_is_valid.
  - apply (frac_eq'_trans _ (Qmul' (Qmul' (fullQ_i x) (fullQ_i y)) (fullQ_i z))).
    2: apply (frac_eq'_trans _ (Qmul' (fullQ_i x) (Qmul' (fullQ_i y) (fullQ_i z)))).
    + apply Qmul'_frac_eq_r; [auto|]. apply frac_eq'_sym. apply fullQ_epi'. 
      now apply Qmul'_valid.
    + rewrite Qmul'_assoc. apply frac_eq'_refl. apply Qmul'_valid; [auto |].
      now apply Qmul'_valid.
    + apply Qmul'_frac_eq_l; [auto|]. apply fullQ_epi'. now apply Qmul'_valid. 
Qed.

Lemma same_is_one (x: Z) `{V: QValid (x, x)} : fullQ_c (x, x) = QPos One.
Proof.
  cbn [fullQ_c]. destruct x. 
  - f_equal. cbn. now rewrite qplus_same'.
  - assert (forall z, ~QValid (z, Zero)) by (intros z H; dependent destruction H).
    exfalso. apply (H Zero V).
  - assert (forall z m, ~QValid (z, Neg m)) by (intros z m H; dependent destruction H).
    exfalso. apply (H (Neg n) n V).
Qed.

Theorem Qmul_inv_r (x: FullQ) : x <> QZero -> x * (Qinv x) = QPos One.
Proof.
  intro H. unfold Qmul. destruct x; cbn.
  - destruct (qplus_i q) as [n d] eqn:E. rewrite (Qplus_inv_in_Q q n d E).
    cbn [Qmul']. rewrite mul_comm. apply same_is_one.
    assert (valid (qplus_i q)) by apply qplus_valid. destruct H0. rewrite E in *.
    cbn in *. destruct n, d; [lia | lia | lia|]. cbn [toPos]. 
    rewrite pos_mul. constructor.
  - contradiction.
  - destruct (qplus_i q) as [n d] eqn:E. rewrite (Qplus_inv_in_Q q n d E).
    cbn [Qmul']. rewrite mul_comm, mul_neg. apply same_is_one.
    assert (valid (qplus_i q)) by apply qplus_valid. destruct H0. rewrite E in *.
    cbn in *. destruct n, d; [lia | lia | lia|]. cbn [toPos]. 
    rewrite pos_mul. constructor.
Qed.

Theorem Qmul_inv_l (x: FullQ) : x <> QZero -> (Qinv x) * x = QPos One.
Proof.
  intros H. now rewrite Qmul_comm, Qmul_inv_r.
Qed.

Theorem Qmul_one_r (x: FullQ) : x * QPos One = x.
Proof.
  unfold Qmul. destruct x; cbn.
  - destruct (qplus_i q) as [n d] eqn:E. cbn [Qmul']. rewrite mul_r_one, mul_r_one.
    assert ((toPos n, toPos d) = fullQ_i (QPos q)) by (cbn; now rewrite E).
    rewrite H. apply fullQ_mono.
  - auto.
  - destruct (qplus_i q) as [n d] eqn:E. cbn [Qmul']. rewrite mul_r_one, mul_r_one.
    assert ((neg (toPos n), toPos d) = fullQ_i (QNeg q)) by (cbn; now rewrite E).
    rewrite H. apply fullQ_mono.
Qed.

Theorem Qmul_one_l (x: FullQ) : QPos One * x  = x.
Proof.
  now rewrite Qmul_comm, Qmul_one_r.
Qed.

Theorem Qmul'_dist (x y z: Q') `{Vx: QValid x} `{Vy: QValid y} `{Vz: QValid z} :
  frac_eq' (Qmul' x (Qadd' y z)) (Qadd' (Qmul' x y) (Qmul' x z)).
Proof.
  dependent destruction Vx. dependent destruction Vy. dependent destruction Vz.
  cbn [Qmul' Qadd']. apply frac_eq'_def.
  - rewrite pos_mul, pos_mul. constructor.
  - rewrite pos_mul, pos_mul, pos_mul. constructor.
  - rewrite mul_l_dist, mul_r_dist, mul_r_dist. f_equal.
    + rewrite (mul_comm (Pos d1) n0), mul_assoc, (mul_comm _ (n * n0)).
      repeat rewrite mul_assoc. f_equal. f_equal.
      repeat rewrite <-mul_assoc. f_equal.
      repeat rewrite pos_mul. f_equal. lia.
    + rewrite (mul_comm (Pos d0) n1), mul_assoc, (mul_comm _ (n * n1)).
      repeat rewrite mul_assoc. f_equal. f_equal.
      repeat rewrite <-mul_assoc. f_equal.
      repeat rewrite pos_mul. f_equal. lia.
Qed.

Theorem Qmul_dist_l (x y z: FullQ) : x * (y + z) = (x * y) + (x * z).
Proof.
  assert (Vx: QValid (fullQ_i x)) by apply fullQ_i_is_valid.
  assert (Vy: QValid (fullQ_i y)) by apply fullQ_i_is_valid.
  assert (Vz: QValid (fullQ_i z)) by apply fullQ_i_is_valid.
  apply fullQ_glue_frac_eq'; unfold Qmul, Qadd.
  - apply Qmul'_valid; apply fullQ_i_is_valid.
  - apply Qadd'_valid; apply fullQ_i_is_valid.
  - apply (frac_eq'_trans _ (Qmul' (fullQ_i x) (Qadd' (fullQ_i y) (fullQ_i z)))).
    2: apply (frac_eq'_trans _ (Qadd' (Qmul' (fullQ_i x) (fullQ_i y)) 
      (Qmul' (fullQ_i x) (fullQ_i z)))).
    3: apply (frac_eq'_trans _ (Qadd' (Qmul' (fullQ_i x) (fullQ_i y)) 
      (fullQ_i (fullQ_c (Qmul' (fullQ_i x) (fullQ_i z)))))).
    + apply Qmul'_frac_eq_l; [auto|]. apply frac_eq'_sym. apply fullQ_epi'. 
      now apply Qadd'_valid.
    + now apply Qmul'_dist.
    + apply Qadd'_frac_eq_l; [now apply Qmul'_valid|]. apply fullQ_epi'. 
      now apply Qmul'_valid.
    + apply Qadd'_frac_eq_r; [now apply fullQ_i_is_valid|]. apply fullQ_epi'. 
      now apply Qmul'_valid.
Qed.

Theorem Qmul_dist_r (x y z: FullQ) : (x + y) * z = (x * z) + (y * z).
Proof.
  now rewrite Qmul_comm, Qmul_dist_l, (Qmul_comm z), (Qmul_comm z).  
Qed.




(* Algebra instances *)
Require Import Lib.Algebra.

Global Program Instance FullQ_is_Group : Group FullQ := {
  zero := QZero;
  op   := Qadd;
  inv  := Qneg;
}.

Next Obligation. apply Qadd_zero_l. Defined.
Next Obligation. apply Qadd_zero_r. Defined.
Next Obligation. apply Qadd_neg_l. Defined.
Next Obligation. apply Qadd_neg_r. Defined.
Next Obligation. apply Qadd_assoc. Defined.

Global Program Instance FullQ_is_Ring : Ring FullQ := {
  one := QPos One;
  mul := Qmul;
}.

Next Obligation. apply Qadd_comm. Defined.
Next Obligation. apply Qmul_one_l. Defined.
Next Obligation. apply Qmul_one_r. Defined.
Next Obligation. apply Qmul_assoc. Defined.
Next Obligation. apply Qmul_dist_l. Defined.
Next Obligation. apply Qmul_dist_r. Defined.

Global Program Instance FullQ_is_RingComm : RingComm FullQ.

Next Obligation. apply Qmul_comm. Defined.

Global Program Instance FullQ_is_Field : Field FullQ := {
  mul_inv := Qinv;
}.

Next Obligation. now apply Qmul_inv_l. Defined.

   