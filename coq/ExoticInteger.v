Require Import Recdef.

Require Import Master.Integer.

Inductive ExoticZ : Type :=
| Zero' : ExoticZ
| MinusOne : ExoticZ
| Next : ExoticZ -> ExoticZ.




(* Add for ExoticZ *)
Function eSucc (k : ExoticZ) : ExoticZ :=
match k with
| Zero' => Next Zero'
| MinusOne => Zero'
| Next Zero' => Next (Next Zero')
| Next MinusOne => MinusOne
| Next k' => Next (eSucc k')
end.

Function ePred (k : ExoticZ) : ExoticZ :=
match k with
| Zero' => MinusOne
| MinusOne => Next MinusOne
| Next Zero' => Zero'
| Next MinusOne => Next (Next MinusOne)
| Next k' => Next (ePred k')
end.

Function eAbs (k: ExoticZ) : nat :=
match k with
| Zero'    => 0
| MinusOne => 1
| Next k'  => S (eAbs k')
end.

Function ePos (k: ExoticZ) : bool :=
match k with
| Zero'    => true
| MinusOne => false
| Next k'  => ePos k'
end.

Definition eAdd (a b : ExoticZ) : ExoticZ :=
match ePos a with 
| true  => map_n (eAbs a) eSucc b
| false => map_n (eAbs a) ePred b
end.

Lemma next_pos_is_same : forall z: ExoticZ, ePos z = ePos (Next z).
Proof.
  intros z. induction z; auto.
Qed.

Lemma if_pos_next_is_succ : forall z: ExoticZ, ePos z = true -> Next z = eSucc z.
Proof.
  intro z. induction z; auto.
  - intros H. cbn in *. discriminate H.
  - intros H. assert (P: ePos z = true) by (rewrite <- H; apply next_pos_is_same; auto).
    cbn. specialize (IHz P). rewrite <- IHz. destruct z; auto. cbn in P. discriminate.
Qed.

Lemma if_neg_next_is_pred : forall z: ExoticZ, ePos z = false -> Next z = ePred z.
Proof.
  intro z. induction z; auto.
  - intros H. cbn in *. discriminate H.
  - intros H. assert (P: ePos z = false) by (rewrite <- H; apply next_pos_is_same; auto).
    cbn. specialize (IHz P). rewrite <- IHz. destruct z; auto. cbn in P. discriminate.
Qed.

Theorem ExoticZ_ind' (P : ExoticZ -> Prop) (base: P Zero') (suc: forall z: ExoticZ, P z -> P (eSucc z)) 
  (pre: forall z: ExoticZ, P z -> P (ePred z)) : forall z: ExoticZ, P z.
Proof.
  intro z. induction z; auto.
  - apply (pre _ base).
  - destruct (ePos z) eqn:pos.
    + rewrite (if_pos_next_is_succ z pos). apply (suc _ IHz).
    + rewrite (if_neg_next_is_pred z pos). apply (pre _ IHz).
Qed.




(* Izomorphism *)
Definition h (n: ExoticZ) : Z :=
match n with
| Zero'    => Zero
| MinusOne => Neg O
| Next n'  => if ePos n' 
              then Pos (eAbs n')
              else Neg (eAbs n')
end.

Definition h_inv (n: Z) : ExoticZ :=
match n with
| Pos n' => map_n (S n') Next Zero'
| Zero   => Zero'
| Neg n' => map_n n' Next MinusOne
end.




Lemma abs_for_map_n : forall n: nat, eAbs (map_n n Next Zero') = n.
Proof.
  intros n. induction n; auto. cbn. f_equal. assumption.
Qed.

Lemma abs_for_map_n' : forall n: nat, eAbs (map_n n Next MinusOne) = S n.
Proof.
  intros n. induction n; auto. cbn. f_equal. assumption.
Qed.

Lemma pos_for_map_n : forall n: nat, ePos (map_n n Next Zero') = true.
Proof.
  intros n. induction n; auto.
Qed.

Lemma pos_for_map_n' : forall n: nat, ePos (map_n n Next MinusOne) = false.
Proof.
  intros n. induction n; auto.
Qed.

Lemma map_n_abs_pos : forall n: ExoticZ, ePos n = true -> map_n (eAbs n) Next Zero' = n.
Proof.
  intros n H. induction n; auto.
  - cbn in *. discriminate.
  - cbn in *. f_equal. apply IHn. assumption. 
Qed.

Lemma map_n_abs_neg : forall n: ExoticZ, ePos n = false -> map_n (eAbs n) Next MinusOne = Next n.
Proof.
  intros n H. induction n; auto.
  - cbn in *. discriminate.
  - cbn in *. f_equal. apply IHn. assumption. 
Qed.



(* Bijection of h function *)
Theorem h_bijection : forall x : Z, h (h_inv x) = x.
Proof.
  intros x. induction x using Z_ind''; [auto| auto | auto |..]; cbn.
  - now rewrite pos_for_map_n, abs_for_map_n.
  - now rewrite pos_for_map_n', abs_for_map_n'.
Qed.

Theorem h_bijection' : forall x : ExoticZ, h_inv (h x) = x.
Proof.
  intros x. destruct x; auto. cbn. destruct (ePos x) eqn:P; cbn.
  - f_equal. now apply map_n_abs_pos.
  - now apply map_n_abs_neg.
Qed.

Lemma h_surjection : forall y: Z, exists x: ExoticZ, h x = y.
Proof.
  intros y. exists (h_inv y). apply h_bijection.
Qed.

Lemma h_iniection : forall x y: ExoticZ, h x = h y -> x = y.
Proof.
  intros x y H. rewrite <- (h_bijection' x), <- (h_bijection' y). f_equal. assumption.
Qed.



Lemma ePred_for_pos : forall x : ExoticZ, ePos x = true -> ePred (Next x) = x.
Proof.
  intros x P. induction x; cbn in *; [auto | discriminate |]. specialize (IHx P).
  now rewrite IHx.
Qed.

Lemma eSucc_for_neg : forall x : ExoticZ, ePos x = false -> eSucc (Next x) = x.
Proof.
  intros x P. induction x; cbn in *; [discriminate | auto |]. specialize (IHx P).
  now rewrite IHx.
Qed.

Lemma ePred_for_neg : forall x : ExoticZ, ePos x = false -> ePred x = Next x.
Proof.
  intros x P. induction x; cbn in *; [discriminate | auto |]. specialize (IHx P).
  rewrite IHx. destruct x; [| auto | auto]. cbn in *. discriminate.
Qed.

Lemma eSucc_for_pos : forall x : ExoticZ, ePos x = true -> eSucc x = Next x.
Proof.
  intros x P. induction x; cbn in *; [auto | discriminate |]. specialize (IHx P).
  rewrite IHx. destruct x; [auto | | auto]. cbn in *. discriminate.
Qed.

Lemma eSucc_ePred: forall k : ExoticZ, eSucc (ePred k) = k.
Proof.
  intros x. functional induction (ePred x); cbn; [auto | auto | auto | auto |]. 
  rewrite IHe. functional induction (ePred k'); cbn; auto. contradiction.
Qed.

Lemma ePred_eSucc : forall k : ExoticZ, ePred (eSucc k) = k.
Proof.
  intros k; functional induction (eSucc k); cbn; [auto | auto | auto | auto |]. 
  rewrite IHe. functional induction (eSucc k'); cbn in *; auto.
  contradiction.
Qed.

Lemma pred_h : forall x: ExoticZ, pred (h x) = h (ePred x).
Proof.
  intro x. destruct (ePos x) eqn:P; destruct x; auto; cbn in P.
  - rewrite ePred_for_pos; auto. cbn. rewrite P.
    destruct x; cbn in *; [auto | discriminate|]. now rewrite P.
  - rewrite ePred_for_neg; auto. cbn. now rewrite P.
Qed.

Lemma succ_h : forall x: ExoticZ, succ (h x) = h (eSucc x).
Proof.
  intro x. destruct (ePos x) eqn:P; destruct x; auto; cbn in P.
  - rewrite eSucc_for_pos; auto. cbn. now rewrite P.
  - rewrite eSucc_for_neg; auto. cbn. rewrite P. 
    destruct x; cbn in *; [auto | auto |]. now rewrite P.
Qed.

Lemma eAdd_l_eSucc : forall x y: ExoticZ, eAdd (eSucc x) y = eSucc (eAdd x y).
Proof.
  intros x y. induction y using ExoticZ_ind'.
  - destruct x; auto. unfold eAdd. destruct (ePos x) eqn:P.
    + rewrite eSucc_for_pos; auto. cbn. now rewrite P.
    + rewrite eSucc_for_neg; auto. cbn. now rewrite P, eSucc_ePred.
  - destruct x; auto.
    + cbn. now  rewrite eSucc_ePred.
    + unfold eAdd. destruct (ePos x) eqn:P.
      * rewrite eSucc_for_pos; auto. cbn. now rewrite P.
      * rewrite eSucc_for_neg; auto. cbn. now rewrite P, eSucc_ePred.
  - destruct x; auto.
    + cbn. now rewrite eSucc_ePred.
    + unfold eAdd. destruct (ePos x) eqn:P.
      * rewrite eSucc_for_pos; auto. cbn. now rewrite P.
      * rewrite eSucc_for_neg; auto. cbn. now rewrite P, eSucc_ePred.
Qed.

Lemma eAdd_l_ePred : forall x y: ExoticZ, eAdd (ePred x) y = ePred (eAdd x y).
Proof.
  intros x y. induction y using ExoticZ_ind'.
  - destruct x; auto. unfold eAdd. destruct (ePos x) eqn:P.
    + rewrite ePred_for_pos; auto. cbn. now rewrite P, ePred_eSucc.
    + rewrite ePred_for_neg; auto. cbn. now rewrite P.
  - destruct x; auto. unfold eAdd. destruct (ePos x) eqn:P.
    + rewrite ePred_for_pos; auto. cbn. now rewrite P, ePred_eSucc.
    + rewrite ePred_for_neg; auto. cbn. now rewrite P.
  - destruct x; auto. unfold eAdd. destruct (ePos x) eqn:P.
    + rewrite ePred_for_pos; auto. cbn. now rewrite P, ePred_eSucc.
    + rewrite ePred_for_neg; auto. cbn. now rewrite P.
Qed.

(* Homomorphism of algebraic structures *)
Theorem Z_ExoticZ_homo : forall x y: ExoticZ, add (h x) (h y) = h (eAdd x y).
Proof.
  intros x y. induction x using ExoticZ_ind'; [auto|..].
  - now rewrite eAdd_l_eSucc, <- succ_h, <- succ_h, <- IHx, add_l_succ.
  - now rewrite eAdd_l_ePred, <- pred_h, <- pred_h, <- IHx, add_l_pred.
Qed.





