Require Import Recdef.
Require Import Integer.

Inductive ExoticZ : Type :=
| Zero' : ExoticZ
| MinusOne : ExoticZ
| Next : ExoticZ -> ExoticZ.




(* Add for ExoticZ *)
Function succ' (k : ExoticZ) : ExoticZ :=
match k with
| Zero' => Next Zero'
| MinusOne => Zero'
| Next Zero' => Next (Next Zero')
| Next MinusOne => MinusOne
| Next k' => Next (succ' k')
end.

Function pred' (k : ExoticZ) : ExoticZ :=
match k with
| Zero' => MinusOne
| MinusOne => Next MinusOne
| Next Zero' => Zero'
| Next MinusOne => Next (Next MinusOne)
| Next k' => Next (pred' k')
end.

Function abs (k: ExoticZ) : nat :=
match k with
| Zero'    => 0
| MinusOne => 1
| Next k'  => S (abs k')
end.

Function pos (k: ExoticZ) : bool :=
match k with
| Zero'    => true
| MinusOne => false
| Next k'  => pos k'
end.

Definition add' (a b : ExoticZ) : ExoticZ :=
match pos a with 
| true  => map_n (abs a) succ' b
| false => map_n (abs a) pred' b
end.

Lemma next_pos_is_same : forall z: ExoticZ, pos z = pos (Next z).
Proof.
  intros z. induction z; auto.
Qed.

Lemma if_pos_next_is_succ : forall z: ExoticZ, pos z = true -> Next z = succ' z.
Proof.
  intro z. induction z; auto.
  - intros H. cbn in *. discriminate H.
  - intros H. assert (P: pos z = true) by (rewrite <- H; apply next_pos_is_same; auto).
    cbn. specialize (IHz P). rewrite <- IHz. destruct z; auto. cbn in P. discriminate.
Qed.

Lemma if_neg_next_is_pred : forall z: ExoticZ, pos z = false -> Next z = pred' z.
Proof.
  intro z. induction z; auto.
  - intros H. cbn in *. discriminate H.
  - intros H. assert (P: pos z = false) by (rewrite <- H; apply next_pos_is_same; auto).
    cbn. specialize (IHz P). rewrite <- IHz. destruct z; auto. cbn in P. discriminate.
Qed.

Theorem ExoticZ_ind' (P : ExoticZ -> Prop) (base: P Zero') (suc: forall z: ExoticZ, P z -> P (succ' z)) 
  (pre: forall z: ExoticZ, P z -> P (pred' z)) : forall z: ExoticZ, P z.
Proof.
  intro z. induction z; auto.
  - apply (pre _ base).
  - destruct (pos z) eqn:pos.
    + rewrite (if_pos_next_is_succ z pos). apply (suc _ IHz).
    + rewrite (if_neg_next_is_pred z pos). apply (pre _ IHz).
Qed.




(* Izomorphism *)
Definition h (n: ExoticZ) : Z :=
match n with
| Zero'    => Zero
| MinusOne => Neg O
| Next n'  => if pos n' 
              then Pos (abs n')
              else Neg (abs n')
end.

Definition h_inv (n: Z) : ExoticZ :=
match n with
| Pos n' => map_n (S n') Next Zero'
| Zero   => Zero'
| Neg n' => map_n n' Next MinusOne
end.




Lemma abs_for_map_n : forall n: nat, abs (map_n n Next Zero') = n.
Proof.
  intros n. induction n; auto. cbn. f_equal. assumption.
Qed.

Lemma abs_for_map_n' : forall n: nat, abs (map_n n Next MinusOne) = S n.
Proof.
  intros n. induction n; auto. cbn. f_equal. assumption.
Qed.

Lemma pos_for_map_n : forall n: nat, pos (map_n n Next Zero') = true.
Proof.
  intros n. induction n; auto.
Qed.

Lemma pos_for_map_n' : forall n: nat, pos (map_n n Next MinusOne) = false.
Proof.
  intros n. induction n; auto.
Qed.

Lemma map_n_abs_pos : forall n: ExoticZ, pos n = true -> map_n (abs n) Next Zero' = n.
Proof.
  intros n H. induction n; auto.
  - cbn in *. discriminate.
  - cbn in *. f_equal. apply IHn. assumption. 
Qed.

Lemma map_n_abs_neg : forall n: ExoticZ, pos n = false -> map_n (abs n) Next MinusOne = Next n.
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
  intros x. destruct x; auto. cbn. destruct (pos x) eqn:P; cbn.
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



Lemma pred'_for_pos : forall x : ExoticZ, pos x = true -> pred' (Next x) = x.
Proof.
  intros x P. induction x; cbn in *; [auto | discriminate |]. specialize (IHx P).
  now rewrite IHx.
Qed.

Lemma succ'_for_neg : forall x : ExoticZ, pos x = false -> succ' (Next x) = x.
Proof.
  intros x P. induction x; cbn in *; [discriminate | auto |]. specialize (IHx P).
  now rewrite IHx.
Qed.

Lemma pred'_for_neg : forall x : ExoticZ, pos x = false -> pred' x = Next x.
Proof.
  intros x P. induction x; cbn in *; [discriminate | auto |]. specialize (IHx P).
  rewrite IHx. destruct x; [| auto | auto]. cbn in *. discriminate.
Qed.

Lemma succ'_for_pos : forall x : ExoticZ, pos x = true -> succ' x = Next x.
Proof.
  intros x P. induction x; cbn in *; [auto | discriminate |]. specialize (IHx P).
  rewrite IHx. destruct x; [auto | | auto]. cbn in *. discriminate.
Qed.

Lemma succ'_pred': forall k : ExoticZ, succ' (pred' k) = k.
Proof.
  intros x. functional induction (pred' x); cbn; [auto | auto | auto | auto |]. 
  rewrite IHe. functional induction (pred' k'); cbn; auto. contradiction.
Qed.

Lemma pred'_succ' : forall k : ExoticZ, pred' (succ' k) = k.
Proof.
  intros k; functional induction (succ' k); cbn; [auto | auto | auto | auto |]. 
  rewrite IHe. functional induction (succ' k'); cbn in *; auto.
  contradiction.
Qed.

Lemma pred_h : forall x: ExoticZ, pred (h x) = h (pred' x).
Proof.
  intro x. destruct (pos x) eqn:P; destruct x; auto; cbn in P.
  - rewrite pred'_for_pos; auto. cbn. rewrite P.
    destruct x; cbn in *; [auto | discriminate|]. now rewrite P.
  - rewrite pred'_for_neg; auto. cbn. now rewrite P.
Qed.

Lemma succ_h : forall x: ExoticZ, succ (h x) = h (succ' x).
Proof.
  intro x. destruct (pos x) eqn:P; destruct x; auto; cbn in P.
  - rewrite succ'_for_pos; auto. cbn. now rewrite P.
  - rewrite succ'_for_neg; auto. cbn. rewrite P. 
    destruct x; cbn in *; [auto | auto |]. now rewrite P.
Qed.

Lemma add'_l_succ' : forall x y: ExoticZ, add' (succ' x) y = succ' (add' x y).
Proof.
  intros x y. induction y using ExoticZ_ind'.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite succ'_for_pos; auto. cbn. now rewrite P.
    + rewrite succ'_for_neg; auto. cbn. now rewrite P, succ'_pred'.
  - destruct x; auto.
    + cbn. now  rewrite succ'_pred'.
    + unfold add'. destruct (pos x) eqn:P.
      * rewrite succ'_for_pos; auto. cbn. now rewrite P.
      * rewrite succ'_for_neg; auto. cbn. now rewrite P, succ'_pred'.
  - destruct x; auto.
    + cbn. now rewrite succ'_pred'.
    + unfold add'. destruct (pos x) eqn:P.
      * rewrite succ'_for_pos; auto. cbn. now rewrite P.
      * rewrite succ'_for_neg; auto. cbn. now rewrite P, succ'_pred'.
Qed.

Lemma add'_l_pred' : forall x y: ExoticZ, add' (pred' x) y = pred' (add' x y).
Proof.
  intros x y. induction y using ExoticZ_ind'.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite pred'_for_pos; auto. cbn. now rewrite P, pred'_succ'.
    + rewrite pred'_for_neg; auto. cbn. now rewrite P.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite pred'_for_pos; auto. cbn. now rewrite P, pred'_succ'.
    + rewrite pred'_for_neg; auto. cbn. now rewrite P.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite pred'_for_pos; auto. cbn. now rewrite P, pred'_succ'.
    + rewrite pred'_for_neg; auto. cbn. now rewrite P.
Qed.

(* Homomorphism of algebraic structures *)
Theorem Z_ExoticZ_homo : forall x y: ExoticZ, add (h x) (h y) = h (add' x y).
Proof.
  intros x y. induction x using ExoticZ_ind'; [auto|..].
  - now rewrite add'_l_succ', <- succ_h, <- succ_h, <- IHx, add_l_succ.
  - now rewrite add'_l_pred', <- pred_h, <- pred_h, <- IHx, add_l_pred.
Qed.





