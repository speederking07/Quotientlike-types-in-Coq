Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Class Group (A : Type) := GroupDef {
  zero      : A;
  op        : A -> A -> A;
  inv       : A -> A;
  eqf       : A -> A -> bool;
  left_id   : forall x: A, op zero x = x;
  right_id  : forall x: A, op x zero = x;
  left_inv  : forall x: A, op (inv x) x = zero;
  right_inv : forall x: A, op x (inv x) = zero;
  op_assoc  : forall x y z: A, op (op x y) z = op x (op y z);
  eqf_eq    : forall x y, reflect (x = y) (eqf x y)
}.

Print reflect.

Lemma eqf_refl {A: Type} `{Group A} (x : A) : eqf x x = true.
Proof.
  destruct (eqf_eq x x); auto.
Qed.

Definition eqf_false {A: Type} `{Group A} {x y: A} : eqf x y = false -> x <> y.
Proof.
  intros H0 H1. subst. rewrite eqf_refl in H0. discriminate.
Defined.

Notation "a @ b" := (op a b) (at level 50).
Notation "c ^" := (inv c) (at level 40).

Definition sub {A: Type} `{Group A} (x y: A) := op x (inv y).

Definition CanonFreeGroup (A: Type) `{Group A} := list (bool*A).

Inductive NonEmptyFreeGroup (A: Type) `{Group A} :=
| Singl  : bool -> A -> NonEmptyFreeGroup A
| Switch : forall x: A, eqf zero x = false -> NonEmptyFreeGroup A -> NonEmptyFreeGroup A
| Stay   : A -> NonEmptyFreeGroup A -> NonEmptyFreeGroup A.

Arguments Switch {A H}.
Arguments Stay {A H}.
Arguments Singl {A H}.

Definition FreeGroup (A: Type) `{Group A} := option (NonEmptyFreeGroup A).

Fixpoint to_uniq' {A: Type} `{Group A} (b : bool) (v: A) (x: CanonFreeGroup A) : NonEmptyFreeGroup A :=
match x with 
| []             => Singl b v
| (b', v') :: x' => if eqb b b' 
                      then Stay (sub v v') (to_uniq' b' v' x')
                      else match eqf zero (sub v v') as i return (eqf zero (sub v v') = i) -> NonEmptyFreeGroup A with
                           | false => fun e => Switch (sub v v') e (to_uniq' b' v' x')
                           | true  => fun _ => (Singl b v) (* invalid *)
                           end eq_refl
end.

Definition to_uniq {A: Type} `{Group A} (x: CanonFreeGroup A) : FreeGroup A :=
match x with
| [] => None
| (b, v) :: x' => Some (to_uniq' b v x')
end.

Fixpoint to_canon' {A: Type} `{Group A} (x: NonEmptyFreeGroup A) : CanonFreeGroup A :=
  match x with 
  | Singl b v   => [(b, v)]
  | Stay v x'   => match to_canon' x' with
                   | [] => [(true, v)] (* should not be there *)
                   | (b, v') :: y => (b, (v @ v')) :: (b, v') :: y
                   end
  | Switch v _ x' => match to_canon' x' with
                               | [] => [(true, v)] (* should not be there *)
                               | (b, v') :: y => (negb b, (v @ v')) :: (b, v') :: y
                               end
  end.

Definition to_canon {A: Type} `{Group A} (x: FreeGroup A) : CanonFreeGroup A :=
  match x with
  | None => []
  | Some x' => to_canon' x'
  end.

Lemma op_sub {A: Type} `{Group A} (x y : A) : op (sub x y) y = x.
Proof.
  unfold sub. rewrite op_assoc. rewrite left_inv. rewrite right_id. auto.
Qed.

Lemma sub_op {A: Type} `{Group A} (x y : A) : sub (op x y) y = x.
Proof.
  unfold sub. rewrite op_assoc. rewrite right_inv. rewrite right_id. auto.
Qed.

Print reflect.

Theorem free_group_epi_cannon {A: Type} `{Group A} (x: FreeGroup A) : 
  to_uniq (to_canon x) = x.
Proof.
  destruct x as [x |].
  - induction x; auto.
    + cbn in *. destruct x0.
      * cbn. f_equal. rewrite eqb_negb1, sub_op. dependent destruction x1.





