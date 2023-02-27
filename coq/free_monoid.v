Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Import ListNotations.

Print list.

Inductive FreeMonoid (A: Type) :=
| leaf : FreeMonoid A
| var  : A -> FreeMonoid A
| op   : FreeMonoid A -> FreeMonoid A -> FreeMonoid A.

Arguments leaf {A}.
Arguments var {A}.
Arguments op {A}.

Fixpoint add_norm {A: Type} (m: FreeMonoid A) (x: A)  : FreeMonoid A :=
match m with
| leaf   => var x
| var y  => op (var y) (var x) 
| op l r => op l (add_norm r x)
end.
 
Fixpoint join_norm {A: Type} (m m': FreeMonoid A) : FreeMonoid A :=
match m' with
| leaf         => m
| var x        => add_norm m x
| op (var x) l => join_norm (add_norm m x) l
| _            => m
end. 

Fixpoint norm {A: Type} (m: FreeMonoid A) : FreeMonoid A :=
match m with
| leaf   => leaf
| var x  => var x
| op l r => join_norm (norm l) (norm r)
end.

Inductive isNorm {A: Type} : FreeMonoid A -> Prop :=
| leafIsNorm : isNorm leaf
| varIsNorm  : forall x: A, isNorm (var x)
| opIsNorm   : forall x: A, forall m : FreeMonoid A, isNorm m -> isNorm (op (var x) m).

Fixpoint to_list {A: Type} (m: FreeMonoid A) : list A :=
match m with
| leaf   => []
| var x  => [x]
| op x y => to_list x ++ to_list y
end.

Definition equiv {A: Type} (m m': FreeMonoid A) : Prop := to_list m = to_list m'.

Theorem add_norm_for_norm : forall A: Type, forall x: A, forall m: FreeMonoid A,
  isNorm m -> isNorm (add_norm m x).
Proof.
  intros A x m H. induction H; cbn; constructor.
  - constructor.
  - assumption.
Qed.

Theorem join_norm_for_norm : forall A: Type, forall x y: FreeMonoid A, 
  isNorm x -> isNorm y -> isNorm (join_norm x y).
Proof.
  intros A x y Hx Hy. revert x Hx. induction Hy; intros z Hz; cbn.
  - assumption.
  - apply add_norm_for_norm. assumption.
  - apply IHHy. apply add_norm_for_norm. assumption.
Qed.

Theorem norm_isNorm : forall A: Type, forall x: FreeMonoid A, isNorm (norm x).
Proof.
  intros A x. induction x; cbn.
  - constructor.
  - constructor.
  - apply join_norm_for_norm; assumption.
Qed.

Theorem add_norm_ok : forall A: Type, forall x: A, forall m : FreeMonoid A, 
  to_list m ++ [x] = to_list (add_norm m x).
Proof.
  intros A x m. induction m; cbn; trivial. rewrite app_assoc_reverse. rewrite IHm2. trivial.
Qed.

Lemma list_with_head_concat : forall A: Type, forall x: A, forall l : list A, 
  x :: l = [x] ++ l.
Proof.
  intros A x m. destruct m; cbn; trivial.
Qed.

Theorem join_norm_ok : forall A: Type, forall x y: FreeMonoid A, 
  isNorm x -> isNorm y -> to_list x ++ to_list y = to_list (join_norm x y).
Proof.
  intros A x y Hx Hy. revert x Hx. induction Hy; intros z Hz; cbn.
  - apply app_nil_r.
  - rewrite add_norm_ok. trivial.
  - rewrite list_with_head_concat. rewrite app_assoc. rewrite add_norm_ok.
    rewrite IHHy. 
    + trivial.
    + apply add_norm_for_norm. assumption.
Qed.

Theorem norm_is_equiv : forall A: Type, forall x: FreeMonoid A, equiv x (norm x).
Proof.
  intros A x. unfold equiv. induction x; cbn; trivial. rewrite IHx1, IHx2.
  apply join_norm_ok; apply norm_isNorm.
Qed.


Lemma leaf_is_nil : forall A: Type, forall m: FreeMonoid A, isNorm m -> equiv m leaf -> m = leaf.
Proof.
  intros A m N H. unfold equiv in H. destruct m.
  - trivial.
  - cbn in H. inversion H.
  - cbn in H.

Theorem uniqe_isNorm : forall A: Type, forall x y: FreeMonoid A,
  isNorm x -> isNorm y -> equiv x y -> x = y.
Proof.
  intros A x y. revert x. induction y.
  - intros x Hx Hy e. unfold equiv in e. cbn in e.
  - intros x Hx Hy e. dependent destruction Hx.
    + inversion e. trivial.
    + unfold equiv in e. cbn in e. inversion e. exfalso. apply (to_list_in_not_nil A m). auto.
  - intros x Hx Hy e. dependent destruction Hy. dependent destruction Hx.
    + unfold equiv in *. cbn in *. inversion e. exfalso. apply (to_list_in_not_nil A y2). auto.
    + rewrite (IHy2 m); trivial.
      * unfold equiv in e. cbn in e. inversion e. trivial.
      * unfold equiv in e. cbn in e. inversion e. assumption.
Qed.

Theorem norm_indepotent : forall A: Type, forall m: FreeMonoid A, norm (norm m) = norm m.
Proof.
  intros A m. apply uniqe_isNorm.
  - apply norm_isNorm.
  - apply norm_isNorm.
  - symmetry. apply norm_is_equiv.
Qed.



