Require Import Recdef.

Inductive Z : Type :=
| Pos : nat -> Z
| Zero : Z
| Neg : nat -> Z.

Inductive Z' : Type :=
| Zero' : Z'
| MinusOne : Z'
| Next : Z' -> Z'.


(* Add for Z *)
Function succ (n: Z) : Z :=
match n with
| Pos k => Pos (S k)
| Zero => Pos O
| Neg O => Zero
| Neg (S n) => Neg n
end.

Function pred (n: Z) : Z :=
match n with
| Pos (S n) => Pos n
| Pos O => Zero
| Zero => Neg O
| Neg n => Neg (S n)
end.

Function map_n {A: Type} (n: nat) (f: A -> A) (x: A) : A :=
match n with
| O => x
| S n' => f (map_n n' f x)
end.

Function add (a b : Z) : Z :=
match a with 
| Pos n => map_n (S n) succ b
| Zero => b
| Neg n => map_n (S n) pred b
end.

Theorem Z_ind' (P : Z -> Prop) (base: P Zero) (base_pos: P (Pos O)) (base_neg: P (Neg O))
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

Theorem succ_pred : forall n: Z, succ (pred n) = n.
Proof.
  intro n. induction n.
  - destruct n; cbn; trivial.
  - cbn. trivial.
  - destruct n; cbn; trivial.
Qed.

Theorem pred_succ : forall n: Z, pred (succ n) = n.
Proof.
  intro n. induction n.
  - destruct n; cbn; trivial.
  - cbn. trivial.
  - destruct n; cbn; trivial.
Qed.


Theorem add_r_zero : forall x: Z, add x Zero = x.
Proof.
  induction x using Z_ind'; trivial.
  - cbn; rewrite succ_S; f_equal; apply IHx.
  - cbn; rewrite pred_S; f_equal; apply IHx.
Qed.

Theorem add_r_succ : forall x y: Z, add x (succ y) = succ (add x y).
Proof.
  intros x y. revert x. induction x using Z_ind'; trivial.
  - cbn. rewrite pred_succ. rewrite succ_pred. trivial.
  - cbn in *. f_equal. apply IHx.
  - cbn in *. rewrite succ_pred. rewrite succ_pred in IHx. rewrite IHx. trivial.
Qed.

Theorem add_r_pred : forall x y: Z, add x (pred y) = pred (add x y).
Proof.
  intros x y. revert x. induction x using Z_ind'; trivial.
  - cbn. rewrite pred_succ. rewrite succ_pred. trivial.
  - cbn in *. rewrite pred_succ in *. rewrite IHx. trivial.
  - cbn in *. f_equal. apply IHx.
Qed.

Theorem add_sym: forall x y: Z, add x y = add y x.
Proof.
  intro x. induction x using Z_ind'; intro y.
  - rewrite add_r_zero. cbn. trivial.
  - cbn. rewrite one_is_zero_succ. rewrite add_r_succ. rewrite add_r_zero. trivial.
  - cbn. rewrite minus_one_is_zero_pred. rewrite add_r_pred.
    rewrite add_r_zero. trivial.
  - cbn. rewrite succ_S. rewrite add_r_succ. f_equal. apply IHx.
  - cbn. rewrite pred_S. rewrite add_r_pred. f_equal. apply IHx.
Qed.


Theorem add_pred_succ : forall x y: Z, add (pred x) (succ y) = add x y.
Proof.
  intros x y. rewrite add_r_succ. rewrite (add_sym (pred x) y). rewrite add_r_pred.
  rewrite succ_pred. rewrite add_sym. trivial.
Qed.


Theorem add_l_succ : forall x y: Z, add (succ x) y = succ (add x y).
Proof.
  intros x y. rewrite (add_sym (succ x) y). rewrite add_r_succ. f_equal.
  apply add_sym.
Qed.

Theorem add_succ_swap : forall x y: Z,  add x (succ y) = add (succ x) y.
Proof.
  intros x y. rewrite add_r_succ. rewrite add_l_succ. trivial.
Qed.

Theorem add_l_pred : forall x y: Z, add (pred x) y = pred (add x y).
Proof.
  intros x y. rewrite (add_sym (pred x) y). rewrite add_r_pred. f_equal.
  apply add_sym.
Qed.

Theorem add_pred_swap : forall x y: Z, add x (pred y) = add (pred x) y.
Proof.
  intros x y. rewrite add_r_pred. rewrite add_l_pred. trivial.
Qed.




(* Add for Z' *)
Function succ' (k : Z') : Z' :=
match k with
| Zero' => Next Zero'
| MinusOne => Zero'
| Next Zero' => Next (Next Zero')
| Next MinusOne => MinusOne
| Next k' => Next (succ' k')
end.

Function pred' (k : Z') : Z' :=
match k with
| Zero' => MinusOne
| MinusOne => Next MinusOne
| Next Zero' => Zero'
| Next MinusOne => Next (Next MinusOne)
| Next k' => Next (pred' k')
end.

Function abs (k: Z') : nat :=
match k with
| Zero'    => 0
| MinusOne => 1
| Next k'  => S (abs k')
end.

Function pos (k: Z') : bool :=
match k with
| Zero'    => true
| MinusOne => false
| Next k'  => pos k'
end.

Definition add' (a b : Z') : Z' :=
match pos a with 
| true  => map_n (abs a) succ' b
| false => map_n (abs a) pred' b
end.

Lemma next_pos_is_same : forall z: Z', pos z = pos (Next z).
Proof.
  intros z. induction z; auto.
Qed.

Lemma if_pos_next_is_succ : forall z: Z', pos z = true -> Next z = succ' z.
Proof.
  intro z. induction z; auto.
  - intros H. cbn in *. discriminate H.
  - intros H. assert (P: pos z = true) by (rewrite <- H; apply next_pos_is_same; auto).
    cbn. specialize (IHz P). rewrite <- IHz. destruct z; auto. cbn in P. discriminate.
Qed.

Lemma if_neg_next_is_pred : forall z: Z', pos z = false -> Next z = pred' z.
Proof.
  intro z. induction z; auto.
  - intros H. cbn in *. discriminate H.
  - intros H. assert (P: pos z = false) by (rewrite <- H; apply next_pos_is_same; auto).
    cbn. specialize (IHz P). rewrite <- IHz. destruct z; auto. cbn in P. discriminate.
Qed.

Theorem Z'_ind' (P : Z' -> Prop) (base: P Zero') (suc: forall z: Z', P z -> P (succ' z)) 
  (pre: forall z: Z', P z -> P (pred' z)) : forall z: Z', P z.
Proof.
  intro z. induction z; auto.
  - apply (pre _ base).
  - destruct (pos z) eqn:pos.
    + rewrite (if_pos_next_is_succ z pos). apply (suc _ IHz).
    + rewrite (if_neg_next_is_pred z pos). apply (pre _ IHz).
Qed.




(* Izomorphism *)
Definition h (n: Z') : Z :=
match n with
| Zero'    => Zero
| MinusOne => Neg O
| Next n'  => if pos n' 
              then Pos (abs n')
              else Neg (abs n')
end.

Definition h_inv (n: Z) : Z' :=
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

Lemma map_n_abs_pos : forall n: Z', pos n = true -> map_n (abs n) Next Zero' = n.
Proof.
  intros n H. induction n; auto.
  - cbn in *. discriminate.
  - cbn in *. f_equal. apply IHn. assumption. 
Qed.

Lemma map_n_abs_neg : forall n: Z', pos n = false -> map_n (abs n) Next MinusOne = Next n.
Proof.
  intros n H. induction n; auto.
  - cbn in *. discriminate.
  - cbn in *. f_equal. apply IHn. assumption. 
Qed.



(* Bijection of h function *)
Theorem h_bijection : forall x : Z, h (h_inv x) = x.
Proof.
  intros x. induction x using Z_ind'; auto.
  - cbn. rewrite pos_for_map_n, abs_for_map_n. auto.
  - cbn. rewrite pos_for_map_n', abs_for_map_n'. auto.
Qed.

Theorem h_bijection' : forall x : Z', h_inv (h x) = x.
Proof.
  intros x. destruct x; auto. cbn. destruct (pos x) eqn:P.
  - cbn. f_equal. apply map_n_abs_pos. assumption.
  - cbn. apply map_n_abs_neg. assumption.
Qed.



Lemma pred'_for_pos : forall x : Z', pos x = true -> pred' (Next x) = x.
Proof.
  intros x P. induction x; cbn in *; try discriminate; auto. specialize (IHx P).
  rewrite IHx. auto.
Qed.

Lemma succ'_for_neg : forall x : Z', pos x = false -> succ' (Next x) = x.
Proof.
  intros x P. induction x; cbn in *; try discriminate; auto. specialize (IHx P).
  rewrite IHx. auto.
Qed.

Lemma pred'_for_neg : forall x : Z', pos x = false -> pred' x = Next x.
Proof.
  intros x P. induction x; cbn in *; try discriminate; auto. specialize (IHx P).
  rewrite IHx. destruct x; auto. cbn in *. discriminate.
Qed.

Lemma succ'_for_pos : forall x : Z', pos x = true -> succ' x = Next x.
Proof.
  intros x P. induction x; cbn in *; try discriminate; auto. specialize (IHx P).
  rewrite IHx. destruct x; auto. cbn in *. discriminate.
Qed.

Lemma succ'_pred': forall k : Z', succ' (pred' k) = k.
Proof.
  intros x. functional induction (pred' x); cbn; auto. rewrite IHz.
  functional induction (pred' k'); cbn; auto. contradiction.
Qed.

Lemma pred'_succ' : forall k : Z', pred' (succ' k) = k.
Proof.
  intros k; functional induction (succ' k); cbn; auto.
  rewrite IHz. functional induction (succ' k'); cbn in *; auto.
  contradiction.
Qed.

Lemma pred_h : forall x: Z', pred (h x) = h (pred' x).
Proof.
  intro x. destruct (pos x) eqn:P.
  - destruct x; auto. cbn in P. rewrite pred'_for_pos; auto.
    cbn. rewrite P. destruct x; cbn in *; try discriminate; auto.
    rewrite P. auto.
  - destruct x; auto. cbn in P. rewrite pred'_for_neg; auto.
    cbn. rewrite P. auto.
Qed.

Lemma succ_h : forall x: Z', succ (h x) = h (succ' x).
Proof.
  intro x. destruct (pos x) eqn:P.
  - destruct x; auto. cbn in P. rewrite succ'_for_pos; auto.
    cbn. rewrite P. auto.
  - destruct x; auto. cbn in P. rewrite succ'_for_neg; auto.
    cbn. rewrite P. destruct x; cbn in *; try discriminate; auto.
    rewrite P. auto.
Qed.

Lemma add'_l_succ' : forall x y: Z', add' (succ' x) y = succ' (add' x y).
Proof.
  intros x y. revert x. induction y using Z'_ind'; auto; intro.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite succ'_for_pos; auto. cbn. rewrite P. auto.
    + rewrite succ'_for_neg; auto. cbn. rewrite P, succ'_pred'. auto.
  - destruct x; auto.
    + cbn. rewrite succ'_pred'. auto.
    + unfold add'. destruct (pos x) eqn:P.
      * rewrite succ'_for_pos; auto. cbn. rewrite P. auto.
      * rewrite succ'_for_neg; auto. cbn. rewrite P, succ'_pred'. auto.
  - destruct x; auto.
    + cbn. rewrite succ'_pred'. auto.
    + unfold add'. destruct (pos x) eqn:P.
      * rewrite succ'_for_pos; auto. cbn. rewrite P. auto.
      * rewrite succ'_for_neg; auto. cbn. rewrite P, succ'_pred'. auto.
Qed.

Lemma add'_l_pred' : forall x y: Z', add' (pred' x) y = pred' (add' x y).
Proof.
  intros x y. revert x. induction y using Z'_ind'; auto; intro.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite pred'_for_pos; auto. cbn. rewrite P, pred'_succ'. auto.
    + rewrite pred'_for_neg; auto. cbn. rewrite P. auto.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite pred'_for_pos; auto. cbn. rewrite P, pred'_succ'. auto.
    + rewrite pred'_for_neg; auto. cbn. rewrite P. auto.
  - destruct x; auto. unfold add'. destruct (pos x) eqn:P.
    + rewrite pred'_for_pos; auto. cbn. rewrite P, pred'_succ'. auto.
    + rewrite pred'_for_neg; auto. cbn. rewrite P. auto.
Qed.

(* Homomorphism of algebraic structures *)
Theorem Z_Z'_homo : forall x y: Z', add (h x) (h y) = h (add' x y).
Proof.
  intros x. induction x using Z'_ind'; auto; intros y.
  - rewrite add'_l_succ', <- succ_h, <- succ_h, <- IHx, add_l_succ. auto.
  - rewrite add'_l_pred', <- pred_h, <- pred_h, <- IHx, add_l_pred. auto.
Qed.





