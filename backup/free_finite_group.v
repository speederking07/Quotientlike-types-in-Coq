Require Import EqNat.
Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.

Record fin (n : nat) := Fin {
  val : nat;
  bound : val < n;
}.

Arguments val {n}.
Arguments bound {n}.

Definition loop_add (x y l: nat) := if Nat.ltb (x + y) l then x + y else x + y - l.

Lemma loop_add_fin (n: nat) (x y: fin n) : loop_add (val x) (val y) n < n.
Proof.
  destruct x, y. cbn. unfold loop_add. destruct (Nat.ltb (val0 + val1) n) eqn:b.
  - rewrite <- PeanoNat.Nat.ltb_lt. assumption.
  - destruct n. 
    + exfalso. apply (PeanoNat.Nat.nlt_0_r val0). assumption.
    + rewrite PeanoNat.Nat.lt_succ_r in *. rewrite PeanoNat.Nat.le_sub_le_add_r.
      apply PeanoNat.Nat.add_le_mono; auto.
Qed.

Definition add {n: nat} (x y : fin n) := 
  Fin n (loop_add (val x) (val y) n) (loop_add_fin n x y).

Definition loop_sub (x y l: nat) := if Nat.ltb x y then x + l - y else x - y.

Lemma loop_sub_fin (n: nat) (x y: fin n) : loop_sub (val x) (val y) n < n.
Proof.
  destruct x, y. cbn. unfold loop_sub. destruct (Nat.ltb val0 val1) eqn:o.
  - destruct n. 
    + exfalso. apply (PeanoNat.Nat.nlt_0_r val0). assumption.
    + rewrite PeanoNat.Nat.ltb_lt in o. rewrite PeanoNat.Nat.lt_succ_r in *. 
      rewrite PeanoNat.Nat.le_sub_le_add_l. rewrite <- PeanoNat.Nat.add_succ_comm.
      apply PeanoNat.Nat.add_le_mono_r. rewrite PeanoNat.Nat.le_succ_l. assumption.
  - destruct n.
    + exfalso. apply (PeanoNat.Nat.nlt_0_r val0). assumption.
    + rewrite PeanoNat.Nat.lt_succ_r in *.
      apply PeanoNat.Nat.le_trans with (m := val0); auto. apply PeanoNat.Nat.le_sub_l.
Admitted.

Definition sub {n: nat} (x y : fin n) := 
  Fin n (loop_sub (val x) (val y) n) (loop_sub_fin n x y).

Lemma prev_fin (n: nat) (x: fin (S (S n))) : (val x) - 1 < S n.
Proof.
  destruct x. cbn. rewrite PeanoNat.Nat.lt_succ_r in *. rewrite PeanoNat.Nat.le_sub_le_add_l.
  rewrite PeanoNat.Nat.add_1_l. assumption.
Qed.

Definition prev {n : nat} (x : fin (S (S n))) := Fin (S n) ((val x) - 1) (prev_fin n x).

Lemma succ_fin (n: nat) (x: fin (n - 1)) : (val x) + 1 < n.
Proof.
  destruct x. cbn. Search (_ + _ < _). rewrite (PeanoNat.Nat.lt_add_lt_sub_r val0 n 1); auto.
Qed.

Definition succ {n : nat} (x : fin (n - 1)) := Fin n ((val x) + 1) (succ_fin n x).



Axiom fin_val_eq : forall (n: nat) (x y : fin n), val x = val y -> x = y.

Lemma add_comm {n : nat} (x y : fin n) : add x y = add y x.
Proof.
  apply fin_val_eq. destruct x, y. cbn. unfold loop_add. rewrite PeanoNat.Nat.add_comm. auto.
Qed.

Lemma add_sub_r {n : nat} (x y : fin n) : add (sub x y) y = x.
Proof.
  apply fin_val_eq. destruct x, y. cbn. unfold loop_add, loop_sub. destruct (Nat.ltb val0 val1) eqn:o.
  - destruct (Nat.ltb (val0 + n - val1 + val1) n) eqn:o2; rewrite PeanoNat.Nat.ltb_lt in *.
    + rewrite (PeanoNat.Nat.sub_add val1), (PeanoNat.Nat.lt_add_lt_sub_r) in o2. 
      * rewrite PeanoNat.Nat.sub_diag in o2. exfalso. apply (PeanoNat.Nat.nlt_0_r val0). auto.
      * rewrite <- (PeanoNat.Nat.add_0_l val1). apply PeanoNat.Nat.add_le_mono.
        -- apply le_0_n.
        -- apply PeanoNat.Nat.lt_le_incl. auto.
    + rewrite <- (PeanoNat.Nat.add_sub_swap (val0 + n) val1 val1).
      * rewrite (PeanoNat.Nat.add_sub (val0 + n) val1), PeanoNat.Nat.add_sub. auto.
      * rewrite <- (PeanoNat.Nat.add_0_l val1). rewrite (PeanoNat.Nat.add_le_mono 0 val0 val1 n); auto.
        -- apply PeanoNat.Nat.le_0_l.
        -- apply PeanoNat.Nat.lt_le_incl. auto.
  - destruct (Nat.ltb (val0 - val1 + val1) n) eqn:o2.
    + rewrite <- PeanoNat.Nat.add_sub_swap.
      * apply PeanoNat.Nat.add_sub.
      * rewrite PeanoNat.Nat.ltb_ge in o. auto.
    + rewrite PeanoNat.Nat.ltb_ge in *. rewrite <- PeanoNat.Nat.add_sub_swap in o2; auto.
      rewrite (PeanoNat.Nat.add_sub val0 val1) in o2. rewrite PeanoNat.Nat.le_ngt in o2.
      contradiction.
Qed.

Lemma sub_add_r {n : nat} (x y : fin n) : sub (add x y) y = x.
Proof.
  apply fin_val_eq. destruct x, y. cbn. unfold loop_add, loop_sub. 
  destruct (Nat.ltb (val0 + val1) n) eqn:o.
  - destruct (Nat.ltb (val0 + val1) val1) eqn:o2; rewrite PeanoNat.Nat.ltb_lt in *.
    + Search (_ + 0 = _). rewrite <- (plus_O_n val1) in o2.
      rewrite PeanoNat.Nat.add_assoc, PeanoNat.Nat.add_0_r  in o2.
      rewrite <- (PeanoNat.Nat.add_lt_mono_r val0 0 val1) in o2.
      exfalso. apply (PeanoNat.Nat.nlt_0_r val0). assumption.
    + rewrite PeanoNat.Nat.add_sub. auto.
  - destruct (Nat.ltb (val0 + val1 - n) val1) eqn:o2.
    + rewrite <- (PeanoNat.Nat.add_sub_swap (val0 + val1) n n).
      * rewrite PeanoNat.Nat.add_sub, PeanoNat.Nat.add_sub. auto.
      * rewrite PeanoNat.Nat.ltb_ge in o; auto.

    + admit.
    
Admitted.

Definition fin_eq {n: nat} (x y : fin n) := Nat.eqb (val x) (val y).
Notation "x =? y" := (fin_eq x y) (at level 10).



Inductive FreeGroup (n: nat) :=
| GNil  : FreeGroup n
| GCons : bool -> fin n -> FreeGroup n -> FreeGroup n.

Arguments GCons {n}.
Arguments GNil {n}.

Fixpoint appinv {n: nat} (x y : FreeGroup n) :=
  match y with 
  | GNil => x
  | GCons b v y' => appinv (GCons b v x) y'
  end.
  

Definition inv {n: nat} (x : FreeGroup n) := appinv GNil x.

(*nf of x^-1 * y *)
Fixpoint norm_stack {n: nat} (x y : FreeGroup n) : FreeGroup n :=
  match x, y with
  | _, GNil                      => inv x
  | GCons b v x', GCons b' v' y' => if (xorb b b') && (v =? v')  
                                    then norm_stack x' y'
                                    else norm_stack (GCons (negb b') v' x) y'
  | _, GCons b v y'              => norm_stack (GCons (negb b) v x) y'
  end.

Fixpoint norm {n: nat} (x: FreeGroup n) := 
  match x with
  | GNil => GNil
  | GCons b v x' => match norm x' with
                    | GNil => GCons b v GNil
                    | GCons b' v' x'' => if (xorb b b') && (v =? v')  
                                         then x''
                                         else (GCons b v (GCons b' v' x'')) 
                    end
  end.

Lemma zero_proof : 0 < 3. 
Proof. auto. Qed.

Lemma one_proof : 1 < 3. 
Proof. auto. Qed.

Lemma two_proof : 2 < 3. 
Proof. auto. Qed.

Definition zero := Fin 3 0 zero_proof.
Definition one := Fin 3 1 one_proof.
Definition two := Fin 3 2 two_proof.

Inductive Normalized {n: nat} : FreeGroup n -> Prop :=
| NNil   : Normalized GNil
| NSingl : forall (b : bool) (v : fin n), Normalized (GCons b v GNil)
| NCons  : forall (b b': bool) (v v' : fin n) (x: FreeGroup n), 
            v =? v' = false \/ xorb b b' = false -> Normalized (GCons  b' v' x) ->
            Normalized (GCons b v (GCons b' v' x)).

Theorem norm_normalize : forall (n: nat) (x: FreeGroup n), Normalized (norm x).
Proof.
  intros n x. induction x.
  - cbn. constructor.
  - cbn. dependent destruction IHx; rewrite <- x.
    + constructor.
    + destruct (xorb b b0 && f =? v) eqn:a.
      * constructor.
      * rewrite andb_false_iff, or_comm in a. constructor; auto. constructor.
    + destruct (xorb b b0 && f =? v) eqn:a.
      * assumption.
      * rewrite andb_false_iff, or_comm in a. constructor; auto. constructor; auto.
Qed.



Inductive UniqNoneEmptyFreeGroup (n: nat) :=
| Switch : fin (n - 1) -> UniqNoneEmptyFreeGroup n -> UniqNoneEmptyFreeGroup n
| Stay   : fin n -> UniqNoneEmptyFreeGroup n -> UniqNoneEmptyFreeGroup n
| Singl  : bool -> fin n -> UniqNoneEmptyFreeGroup n.

Definition UniqFreeGroup (n: nat) := option (UniqNoneEmptyFreeGroup n).

Arguments Switch {n}.
Arguments Stay {n}.
Arguments Singl {n}.

Print option.

Definition trans {A: Type} {P : A -> Type} {x y: A} (p : x = y) (t : P x) : P y :=
  match p with
  | eq_refl => t
  end.

Lemma eq_prev (n n' : nat) (H : n = S (S n')) : S n' = n - 1.
Proof.
  subst. auto.
Qed.

Fixpoint to_uniq' {n: nat} (b : bool) (v: fin n) (x: FreeGroup n) : UniqNoneEmptyFreeGroup n :=
match x with 
| GNil           => Singl b v
| GCons b' v' x' => if xorb b b' 
                    then match n as n_ return (n = n_) -> UniqNoneEmptyFreeGroup n with
                         | S (S n') => fun e => Switch (trans (eq_prev n n' e) (prev (trans e (sub v v')))) (to_uniq' b' v' x')
                         | _ => fun e => (Singl b v) (* invalid *)
                         end eq_refl
                    else Stay (sub v v') (to_uniq' b' v' x')
end.

Definition to_uniq {n: nat} (x: FreeGroup n) : UniqFreeGroup n :=
match x with
| GNil => None
| GCons b v x' => Some (to_uniq' b v x')
end.

(* Fixpoint to_uniq {n: nat} (x: FreeGroup n) : UniqFreeGroup n :=
match x with 
| GCons b v x' => match x' with 
                  | GNil            => Some (Singl b v)
                  | GCons b' v' x'' => if xorb b b' 
                                       then match n as n_ return (n = n_) -> UniqFreeGroup n with
                                            | S (S n') => fun e => option_map (fun u => Switch (trans (eq_prev n n' e) (prev (trans e (sub v v')))) u) (to_uniq x')
                                            | _ => fun e => None (* invalid *)
                                            end eq_refl
                                       else option_map (fun u => Stay (sub v v') u) (to_uniq x')
                  end
| GNil         => None
end. *)

Print Bool.

Fixpoint to_free_group' {n: nat} (x: UniqNoneEmptyFreeGroup n) : FreeGroup n :=
  match x with 
  | Singl b v   => GCons b v GNil
  | Stay v x'   => match to_free_group' x' with
                   | GNil => GCons true v GNil (* should not be there *)
                   | GCons b v' y => GCons b (add v v') (GCons b v' y)
                   end
  | Switch v x' => match to_free_group' x' with
                   | GNil => GCons true (succ v) GNil (* should not be there *)
                   | GCons b v' y => GCons (negb b) (add (succ v) v') (GCons b v' y)
                   end
  end.

Definition to_free_group {n: nat} (x: UniqFreeGroup n) : FreeGroup n :=
  match x with
  | None => GNil
  | Some x' => to_free_group' x'
  end.

Lemma to_free_group'_empty {n : nat} (x : UniqNoneEmptyFreeGroup n) : ~ (to_free_group' x = GNil).
Proof.
  intros H. destruct x.
  - cbn in *. destruct (to_free_group' x); inversion H.
  - cbn in *. destruct (to_free_group' x); inversion H.
  - cbn in *. inversion H.
Qed.

Lemma to_free_group_empty {n : nat} (x : UniqFreeGroup n) : to_free_group x = GNil <-> x = None.
Proof.
  split.
  - intros H. destruct x; auto. exfalso. apply (to_free_group'_empty u). cbn in H. assumption.
  - intros H. subst. auto.
Qed.



Theorem to_free_group_to_uniq (n : nat) (x : UniqFreeGroup n) : to_uniq (to_free_group x) = x.
Proof.
  destruct n; try destruct n.
  - destruct x; auto. destruct u; auto.
    + destruct f. cbn in bound0. exfalso. apply (PeanoNat.Nat.nlt_0_r val0). assumption.
    + destruct f. cbn in bound0. exfalso. apply (PeanoNat.Nat.nlt_0_r val0). assumption.
  - destruct x; auto. cbn. induction u; auto.
    + destruct f. cbn in bound0. exfalso. apply (PeanoNat.Nat.nlt_0_r val0). assumption.
    + cbn. destruct (to_free_group' u) eqn:e.
      * cbn in *. inversion IHu.
      * cbn in *. rewrite xorb_nilpotent. inversion IHu. rewrite H0 in *.
        f_equal. f_equal. rewrite sub_add_r. auto.
  - destruct x; auto. cbn. induction u; auto.
    + cbn in *. destruct (to_free_group' u) eqn:e.
      * cbn in *. inversion IHu.
      * cbn in *. inversion IHu. rewrite H0 in *. rewrite <- (negb_xorb_l b b), xorb_nilpotent.
        cbn. f_equal. f_equal. rewrite sub_add_r.


Eval simpl in to_free_group (to_uniq (GCons true two (GCons true one (GCons false zero GNil)))).

