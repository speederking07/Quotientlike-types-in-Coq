Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import StrictProp.
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

Lemma eqf_refl {A: Type} `{Group A} (x : A) : eqf x x = true.
Proof.
  destruct (eqf_eq x x); auto.
Qed.

Definition eqf_true_iff {A: Type} `{Group A} {x y: A} : eqf x y = true <-> x = y.
Proof.
  destruct (eqf_eq x y); split; auto. intros F. discriminate.
Qed.

Definition eqf_false_iff {A: Type} `{Group A} {x y: A} : eqf x y = false <-> x <> y.
Proof.
  split.
  - intros H0 H1. subst. rewrite eqf_refl in H0. discriminate.
  - intros H0. destruct (eqf_eq x y); auto. subst. contradiction.
Defined.

Lemma eqf_sym {A: Type} `{Group A} (x y: A) : eqf x y = eqf y x.
Proof.
  destruct (eqf_eq x y).
  - subst. rewrite eqf_refl. auto.
  - assert (y <> x) by (apply not_eq_sym; auto). rewrite <- eqf_false_iff in H0.
    rewrite H0. auto.
Qed.


(* Notation "a @ b" := (op a b) (at level 51, right associativity).
Notation "c ^" := (inv c) (at level 40). *)

Definition sub {A: Type} `{Group A} (x y: A) := op x (inv y).

Definition CanonFreeGroup (A: Type) `{Group A} := list (bool*A).

Inductive Normalized {A: Type} `{Group A} : CanonFreeGroup A -> Prop :=
| NNil   : Normalized []
| NSingl : forall (b : bool) (v : A), Normalized [(b, v)]
| NCons  : forall (b b': bool) (v v' : A) (x: CanonFreeGroup A), 
            v <> v' \/ b = b' -> Normalized ((b', v') :: x) ->
            Normalized ((b, v) :: (b', v') :: x).

Inductive NonEmptyFreeGroup (A: Type) `{Group A} :=
| Singl  : bool -> A -> NonEmptyFreeGroup A
| Switch : forall x: A, Squash (x <> zero) -> NonEmptyFreeGroup A -> NonEmptyFreeGroup A
| Stay   : A -> NonEmptyFreeGroup A -> NonEmptyFreeGroup A.

Arguments Switch {A H}.
Arguments Stay {A H}.
Arguments Singl {A H}.

Definition FreeGroup (A: Type) `{Group A} := option (NonEmptyFreeGroup A).

Print reflect.

Fixpoint to_uniq' {A: Type} `{Group A} (b : bool) (v: A) (x: CanonFreeGroup A) : NonEmptyFreeGroup A :=
match x with 
| []             => Singl b v
| (b', v') :: x' => if eqb b b' 
                      then Stay (sub v v') (to_uniq' b' v' x')
                      else match eqf_eq (sub v v') zero with
                           | ReflectF _ p => Switch (sub v v') (squash p) (to_uniq' b' v' x')
                           | _  => (Singl b v) (* invalid *)
                           end
end.

Definition to_uniq {A: Type} `{Group A} (x: CanonFreeGroup A) : FreeGroup A :=
match x with
| [] => None
| (b, v) :: x' => Some (to_uniq' b v x')
end.

Fixpoint to_canon' {A: Type} `{Group A} (x: NonEmptyFreeGroup A) : CanonFreeGroup A :=
  match x with 
  | Singl b v     => [(b, v)]
  | Stay v x'     => match to_canon' x' with
                     | [] => [(true, v)] (* should not be there *)
                     | (b, v') :: y => (b, op v v') :: (b, v') :: y
                     end
  | Switch v _ x' => match to_canon' x' with
                     | [] => [(true, v)] (* should not be there *)
                     | (b, v') :: y => (negb b, op v v') :: (b, v') :: y
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

Lemma squash_not_refl {A : Type} (x: A) (P: Prop) : Squash (x <> x) -> P.
Proof.
  intros H. apply sEmpty_ind. apply (Squash_sind (x <> x)); auto.
  intro H0. exfalso. apply H0. auto.
Qed.

Lemma not_eqb_is_neg (x y : bool) : eqb x y = false -> x = negb y.
Proof.
  intros H. destruct x, y; cbn in *; auto; try inversion H.
Qed.

Lemma some_eq {A: Type} (x y: A) : Some x = Some y -> x = y.
Proof.
  intros H. inversion H. auto.
Qed.

Lemma eqb_not_neg (x y : bool) : eqb x (negb y) = false <-> x = y.
Proof.
  split.
  - intros H. destruct x, y; auto; try inversion H.
  - intros H. subst. destruct y; auto.
Qed.

Lemma group_equation_l_simp {A: Type} `{Group A} (a b c : A) : op a b = op a c -> b = c.
Proof.
  intro H0. assert (op (inv a) (op a b) = op (inv a) (op a c)).
  - rewrite H0. auto.
  - rewrite <- op_assoc, <- op_assoc, left_inv, left_id, left_id in H1. auto.
Qed.

Lemma group_equation_r_simp {A: Type} `{Group A} (a b c : A) : op a c = op b c -> a = b.
Proof.
  intro H0. assert (op (op a c) (inv c) = op (op b c) (inv c)).
  - rewrite H0. auto.
  - rewrite op_assoc, op_assoc, right_inv, right_id, right_id in H1. auto.
Qed.

Lemma sub_inv_uniq {A: Type} `{Group A} (x y: A) : sub x y = zero -> x = y.
Proof.
  unfold sub. rewrite <- (right_inv y). intros H0. 
  apply group_equation_r_simp with (c := inv y). auto.
Qed.

Theorem free_group_epi_canon {A: Type} `{Group A} (x: FreeGroup A) : 
  to_uniq (to_canon x) = x.
Proof.
  destruct x as [x |]; auto. induction x; auto.
  - cbn in *. destruct (to_canon' x0); inversion IHx. destruct p. cbn in *. 
    inversion IHx. subst. rewrite eqb_negb1, sub_op. destruct (eqf_eq x zero); auto.
    subst. apply (squash_not_refl zero); auto.
  - cbn in *. destruct (to_canon' x); inversion IHx. destruct p. cbn in *.
    inversion IHx. subst. rewrite eqb_reflx, sub_op. auto.
Qed.

Theorem canon_epi_free_group {A: Type} `{Group A} (x: CanonFreeGroup A) : 
  Normalized x -> to_canon (to_uniq x) = x.
Proof.
  intros N. induction N; auto. cbn in *. destruct H0 as [v_neq | b_neq].
  - destruct (eqb b b') eqn:b_eq.
    + cbn. rewrite IHN, op_sub. f_equal. f_equal. symmetry. apply eqb_prop. auto.
    + destruct (eqf_eq (sub v v') zero).
      * assert (v = v') by (apply sub_inv_uniq; auto). contradiction.
      * cbn. rewrite IHN, op_sub. f_equal. f_equal. symmetry. apply not_eqb_is_neg. auto.
  - subst. rewrite eqb_reflx. cbn. rewrite IHN, op_sub. auto.
Qed.

Lemma to_canon'_not_nil {A: Type} `{Group A} (x: NonEmptyFreeGroup A) : to_canon' x <> nil.
Proof.
  intros H0. destruct x; cbn in *.
  - inversion H0.
  - destruct (to_canon' x0).
    + inversion H0.
    + destruct p. inversion H0.
  - destruct (to_canon' x).
    + inversion H0.
    + destruct p. inversion H0.
Qed.

Lemma group_add_non_zero {A: Type} `{Group A} (x y : A) : x <> zero -> op x y <> y.
Proof.
  intros H0 H1. apply H0. apply group_equation_r_simp with (c := op y (inv y)).
  rewrite <- op_assoc, H1, right_inv, left_id. auto.
Qed.

Lemma group_squash_non_zero {A: Type} `{Group A} (x : A) : Squash (x <> zero) -> x <> zero.
Proof.
  intros H0. destruct (eqf_eq x zero); auto. subst. apply (squash_not_refl zero). auto.
Qed. 

Theorem free_group_is_normal {A: Type} `{Group A} (x: FreeGroup A) : Normalized (to_canon x).
Proof.
  destruct x as [x |].
  - induction x.
    + cbn. constructor.
    + dependent destruction IHx.
      * assert (to_canon (Some x0) <> []) by (apply to_canon'_not_nil). rewrite x in H0.
        contradiction.
      * cbn in *. rewrite <- x. constructor; constructor. apply group_add_non_zero. 
        apply group_squash_non_zero. auto.
      * cbn in *. rewrite <- x. constructor.
        -- left. apply group_add_non_zero. apply group_squash_non_zero. auto.
        -- constructor; auto.
    + dependent destruction IHx.
      * assert (to_canon (Some x0) <> []) by (apply to_canon'_not_nil). rewrite x in H0.
        contradiction.
      * cbn in *. rewrite <- x. constructor; try right; constructor.
      * cbn in *. rewrite <- x. constructor; try right; constructor; auto.
  - cbn. constructor.
Qed.

Definition option_bind {A B: Type} (x: option A) (f: A -> option B) : option B :=
  match x with
  | None => None
  | Some x' => f x'
  end. 

Fixpoint fg_hd' {A: Type} `{Group A} (x: NonEmptyFreeGroup A) : bool * A :=
  match x with 
  | Singl b v => (b, v)
  | Stay v x' => let (b', v') := fg_hd' x' in (b', op v v')
  | Switch v _ x' => let (b', v') := fg_hd' x' in (negb b', op v v')
  end.

Definition fg_hd {A: Type} `{Group A} (x: FreeGroup A) : option (bool * A) :=
  option_map fg_hd' x.

Theorem fg_hd_for_canon {A: Type} `{Group A} (x: CanonFreeGroup A) :
  Normalized x -> hd_error x = fg_hd (to_uniq x).
Proof.
  intros H0. induction H0; auto. cbn in *. f_equal. inversion IHNormalized. destruct H0.
  - destruct (eqb b b') eqn:e.
    + cbn. rewrite <- H3, op_sub. rewrite eqb_true_iff in e. f_equal; auto.
    + destruct (eqf_eq (sub v v') zero); auto. cbn. rewrite <- H3, op_sub. f_equal.
      apply not_eqb_is_neg. auto.
  - subst. rewrite eqb_reflx. cbn. rewrite <- H3, op_sub. auto.
Qed.

Definition fq_tail' {A: Type} `{Group A} (x: NonEmptyFreeGroup A) : FreeGroup A :=
  match x with 
  | Singl _ _     => None
  | Stay _ x'     => Some x'
  | Switch _ _ x' => Some x'
  end.

Definition fg_tail {A: Type} `{Group A} (x: FreeGroup A) : FreeGroup A :=
  option_bind x fq_tail'.

Definition fg_cons' {A: Type} `{Group A} (b: bool) (v: A) (x: NonEmptyFreeGroup A) : 
   FreeGroup A :=
    let (b', v') := fg_hd' x in 
      if eqb b b'
      then Some (Stay (sub v v') x)
      else match eqf_eq (sub v v') zero with
           | ReflectT _ _ => fq_tail' x
           | ReflectF _ p => Some (Switch (sub v v') (squash p) x)
           end.

Definition fg_cons'2 {A: Type} `{Group A} (p : bool * A) (x: NonEmptyFreeGroup A) :=
  let (b, v) := p in fg_cons' b v x.

Definition fg_cons {A: Type} `{Group A} (b: bool) (v: A) (x: FreeGroup A) : FreeGroup A :=
  match x with
  | None => Some (Singl b v)
  | Some x' => fg_cons' b v x'
  end.

Definition fg_cons2 {A: Type} `{Group A} (p: bool * A) (x: FreeGroup A) : FreeGroup A := 
  let (b, v) := p in fg_cons b v x.
 
Definition elem_inv {A: Type} (x : bool * A) := let (b, v) := x in (negb b, v).

Theorem inv_elem_cons_is_tail {A: Type} `{Group A} (x: NonEmptyFreeGroup A) :
  fg_cons'2 (elem_inv (fg_hd' x)) x = fq_tail' x.
Proof.
  destruct (fg_hd' x) eqn:hd. destruct x; cbn.
  - inversion hd. unfold sub. rewrite eqb_negb1, right_inv.
    destruct (eqf_eq zero zero); auto. contradiction.
  - unfold fg_cons', sub. rewrite hd, eqb_negb1, right_inv. 
    destruct (eqf_eq zero zero); auto. contradiction.
  - unfold fg_cons', sub. rewrite hd, eqb_negb1, right_inv. 
    destruct (eqf_eq zero zero); auto. contradiction.
Qed.

Definition canon_cons {A: Type} `{Group A} (b: bool) (v: A) (x: CanonFreeGroup A) :
  CanonFreeGroup A :=
  match x with
  | [] => [(b, v)]
  | (b', v') :: t => if negb (eqf v v') || eqb b b'
                     then (b, v) :: (b', v') :: t
                     else t
  end.

Fixpoint canon_concat {A: Type} `{Group A} (x y: CanonFreeGroup A) : CanonFreeGroup A :=
  match x with
  | []           => y
  | (b, v) :: x' => canon_cons b v (canon_concat x' y)
  end.

Definition fg_canon_concat {A: Type} `{Group A} (x y: FreeGroup A) : FreeGroup A :=
  to_uniq (canon_concat (to_canon x) (to_canon y)).

Theorem concat_norm {A: Type} `{Group A} (x y: CanonFreeGroup A) : 
  Normalized x -> Normalized y -> Normalized (canon_concat x y).
Proof.
  intros Nx Ny. induction Nx; auto.
  - cbn. destruct Ny; unfold canon_cons.
    + constructor.
    + destruct (negb (eqf v v0) || eqb b b0 ) eqn:e; constructor.
      * rewrite orb_true_iff, eqb_true_iff, negb_true_iff, eqf_false_iff in e. auto.
      * constructor.
    + destruct (negb (eqf v v0) || eqb b b0) eqn:e; auto. constructor.
      * rewrite orb_true_iff, eqb_true_iff, negb_true_iff, eqf_false_iff in e. auto.
      * constructor; auto.
  - cbn. destruct (canon_concat x y) eqn:c; unfold canon_cons in *.
    + assert (negb (eqf v v') || eqb b b' = true).
      * rewrite orb_true_iff, eqb_true_iff, negb_true_iff, eqf_false_iff. auto.
      * rewrite H1. constructor; auto. constructor.
    + destruct p. cbn in *. rewrite c in IHNx. destruct (negb (eqf v' a) || eqb b' b0) eqn:e.
      * assert (negb (eqf v v') || eqb b b' = true); unfold canon_cons in *.
        -- rewrite orb_true_iff, eqb_true_iff, negb_true_iff, eqf_false_iff. auto.
        -- rewrite H1. rewrite e in IHNx. constructor; auto.
      * cbn in *. destruct c0; try constructor. destruct p.
        destruct (negb (eqf v a0) || eqb b b1) eqn:e1; unfold canon_cons in *; rewrite e in IHNx.
        -- constructor; auto.
           rewrite orb_true_iff, eqb_true_iff, negb_true_iff, eqf_false_iff in e1. auto.
        -- dependent destruction IHNx; auto. constructor.
Qed.

Fixpoint fg_concat' {A: Type} `{Group A} (x: NonEmptyFreeGroup A) 
  (y: FreeGroup A) : FreeGroup A :=
  match x with
  | Singl b v     => fg_cons b v y
  | Stay _ x'     => fg_cons2 (fg_hd' x) (fg_concat' x' y)
  | Switch _ _ x' => fg_cons2 (fg_hd' x) (fg_concat' x' y)
  end.

Definition fg_concat {A: Type} `{Group A} (x y: FreeGroup A) : FreeGroup A :=
  match x with
  | None => y
  | Some x' => fg_concat' x' y
  end.

Lemma eqf_sub_not_zero {A: Type} `{Group A} (x y: A) : sub x y <> zero <-> eqf x y = false.
Proof.
  unfold sub. split.
  - intros H0. destruct (eqf_eq x y); auto. subst. rewrite right_inv in H0. 
    contradiction.
  - intros H0 H1. assert (x = y) by (apply sub_inv_uniq; auto). subst.
    rewrite eqf_refl in H0. discriminate.
Qed.

Theorem free_canon_hd'_izo {A: Type} `{Group A} (x: NonEmptyFreeGroup A) :
  Some (fg_hd' x) = hd_error (to_canon (Some x)).
Proof.
  induction x; auto.
  - cbn in *. destruct (to_canon' x0) eqn:e.
    + exfalso. apply (to_canon'_not_nil x0). auto.
    + destruct p. cbn in *. inversion IHx. rewrite H1. auto.
  - cbn in *. destruct (to_canon' x) eqn:e.
    + exfalso. apply (to_canon'_not_nil x). auto.
    + destruct p. cbn in *. inversion IHx. rewrite H1. auto.
Qed.

Theorem free_canon_hd_izo {A: Type} `{Group A} (x: FreeGroup A) :
  fg_hd x = hd_error (to_canon x).
Proof.
  destruct x as [x |]; auto. cbn. apply free_canon_hd'_izo.
Qed.

Theorem free_canon_cons_izo {A: Type} `{Group A} (b: bool) (v: A) (x: FreeGroup A) :
  to_canon (fg_cons b v x) = canon_cons b v (to_canon x).
Proof.
  destruct x as [x |]; auto. unfold canon_cons. destruct x.
  - cbn. destruct (eqb b b0) eqn:e.
    + cbn. rewrite orb_true_r, op_sub. rewrite eqb_true_iff in e. subst. auto.
    + destruct (eqf_eq (sub v a) zero).
      * assert (v = a) by (apply sub_inv_uniq; auto). subst.
        rewrite eqf_refl. cbn. auto.
      * cbn. rewrite eqf_sub_not_zero in n. rewrite n, op_sub. cbn.
        assert (negb b0 = b) by (symmetry; apply not_eqb_is_neg; auto). 
        subst. auto.
  - cbn. destruct (to_canon' x0) eqn:c.
    + exfalso. apply (to_canon'_not_nil x0). auto.
    + destruct p. unfold fg_cons'. cbn. assert (hd_eq : fg_hd' x0 = (b0, a)).
      { apply some_eq. rewrite free_canon_hd'_izo. cbn. rewrite c. auto. }
      rewrite hd_eq. destruct (eqb b (negb b0)) eqn:eb.
      * cbn. rewrite orb_true_r, c, op_sub. rewrite eqb_true_iff in eb. subst.
        auto.
      * destruct (eqf_eq (sub v (op x a))).
        -- assert (v = (op x a)) by (apply sub_inv_uniq; auto). subst.
          rewrite eqf_refl. cbn. auto.
        -- cbn. rewrite eqf_sub_not_zero in n. rewrite n, c. unfold sub. cbn.
           rewrite (op_assoc  v (inv (op x a))), left_inv, right_id, negb_involutive.
           f_equal. rewrite eqb_not_neg in eb. subst. auto.
  - cbn. destruct (to_canon' x) eqn:c.
    + exfalso. apply (to_canon'_not_nil x). auto.
    + destruct p. unfold fg_cons'. cbn. assert (hd_eq : fg_hd' x = (b0, a0)).
      { apply some_eq. rewrite free_canon_hd'_izo. cbn. rewrite c. auto. }
      rewrite hd_eq. destruct (eqb b b0) eqn:eb.
      * cbn. rewrite orb_true_r, c, op_sub. rewrite eqb_true_iff in eb. subst.
        auto.
      * destruct (eqf_eq (sub v (op a a0))).
        -- assert (v = (op a a0)) by (apply sub_inv_uniq; auto). subst.
          rewrite eqf_refl. cbn. auto.
        -- cbn. rewrite eqf_sub_not_zero in n. rewrite n, c. unfold sub. cbn.
           rewrite (op_assoc  v (inv (op a a0))), left_inv, right_id.
           f_equal. assert (b = negb b0) by (apply not_eqb_is_neg; auto).
           subst. auto.
Qed.

Theorem free_canon_concat_izo {A: Type} `{Group A} (x y: FreeGroup A) :
  to_canon (fg_concat x y) = canon_concat (to_canon x) (to_canon y).
Proof.
  destruct x as [x |]; auto. cbn. induction x.
  - cbn. apply free_canon_cons_izo.
  - cbn. destruct (to_canon' x0) eqn:c.
    + exfalso. apply (to_canon'_not_nil x0). auto.
    + destruct p. assert (hd_eq : fg_hd' x0 = (b, a)).
      { apply some_eq. rewrite free_canon_hd'_izo. cbn. rewrite c. auto. }
      rewrite hd_eq. cbn in *. rewrite <- IHx. apply free_canon_cons_izo.
  - cbn. destruct (to_canon' x) eqn:c.
    + exfalso. apply (to_canon'_not_nil x). auto.
    + destruct p. assert (hd_eq : fg_hd' x = (b, a0)).
      { apply some_eq. rewrite free_canon_hd'_izo. cbn. rewrite c. auto. }
      rewrite hd_eq. cbn in *. rewrite <- IHx. apply free_canon_cons_izo.
Qed.

Fixpoint canon_apinv {A: Type} `{Group A} (x y: CanonFreeGroup A) :=
  match x with
  | [] => y
  | (b, v) :: x' => canon_apinv x' (cons (negb b, v) y)
  end.

Definition canon_inv {A: Type} `{Group A} (x: CanonFreeGroup A) := canon_apinv x [].

Fixpoint canon_append {A: Type} `{Group A} (b: bool) (v: A) (x: CanonFreeGroup A) :=
  match x with
  | [] => [(b, v)]
  | [(b', v')] => if negb (eqf v v') || eqb b b'
                     then [(b', v'); (b, v)]
                     else []
  | h :: x' => h :: (canon_append b v x')
  end.

Theorem group_inv_inv {A: Type} `{Group A} (x: A) : inv (inv x) = x.
Proof.
  rewrite <- (right_id (inv (inv x))), <- (left_inv x), <- (op_assoc), left_inv, left_id.
  auto.
Qed.

Lemma eqb_sym (x y : bool) : eqb x y = eqb y x.
Proof.
  destruct x, y; auto.
Qed.

Lemma eqb_both_neg (x: bool) : eqb (negb x) (negb x) = true.
Proof.
  destruct x; auto.
Qed.

Lemma eqb_false_chain (x y z: bool) : eqb x y = false -> eqb y z = false -> x = z.
Proof.
  intros H H0. destruct x, y, z; auto; cbn in *; discriminate.
Qed.

Lemma condition_iff {A: Type} `{Group A} (b b': bool) (v v': A) :
  v <> v' \/ b = b' <-> negb (eqf v v') || eqb b b' = true.
Proof.
  split.
  - intros [|].
    + rewrite <- eqf_false_iff in H0. rewrite H0. auto.
    + subst. rewrite eqb_reflx, orb_true_r. auto.
  - intro H0. rewrite orb_true_iff, negb_true_iff in H0. destruct H0.
    + left. rewrite <- eqf_false_iff. auto.
    + right. apply eqb_prop. auto.
Qed.

Lemma condition_false_iff {A: Type} `{Group A} (b b': bool) (v v': A) :
  v = v' /\ b = negb b' <-> negb (eqf v v') || eqb b b' = false.
Proof.
  split.
  - intros []. subst. rewrite eqf_refl, eqb_negb1. auto.
  - intro H0. rewrite orb_false_iff, negb_false_iff in H0. destruct H0. split.
    + rewrite <- eqf_true_iff. auto.
    + destruct b, b'; auto; cbn in *; try discriminate.
Qed.

Lemma canon_cons_inv_elem {A: Type} `{Group A} (b b': bool) (v v': A) (x: CanonFreeGroup A) :
  Normalized x -> negb (eqf v v') || eqb b b' = false -> canon_cons b v (canon_cons b' v' x) = x.
Proof.
  intros Nx H0. induction Nx as [| b'' v'' | b'' b''' v'' v'''].
  - cbn. rewrite H0. auto.
  - cbn. destruct (negb (eqf v' v'') || eqb b' b'') eqn:H1.
    + cbn. rewrite H0. auto.
    + cbn. rewrite orb_false_iff, negb_false_iff in H0, H1. destruct H0, H1.
      rewrite eqf_true_iff in H0. rewrite eqf_true_iff in H1. subst. f_equal. f_equal.
      apply eqb_false_chain with (y := b'); auto.
  - rewrite condition_iff in H1. cbn. destruct (negb (eqf v' v'') || eqb b' b'') eqn:H2.
    + cbn. rewrite H0. auto.
    + cbn in *. rewrite <- condition_false_iff in H0, H2.
      destruct H0, H2. subst. rewrite negb_involutive, H1. auto.
Qed.

Lemma normalized_without_head {A: Type} `{Group A} (b: bool) (v: A) (x: CanonFreeGroup A) :
  Normalized ((b, v) :: x) -> Normalized x.
Proof.
  intros Nx. destruct x.
  - constructor.
  - destruct p as (b', v'). dependent destruction Nx. auto.
Qed.

Lemma canon_concat_cons {A: Type} `{Group A} (b: bool) (v: A) (x y: CanonFreeGroup A) :
  Normalized x -> Normalized y -> canon_concat (canon_cons b v x) y  = canon_cons b v (canon_concat x y).
Proof.
  intros Nx Ny. destruct x as [| (b' & v') x']; auto. cbn. 
  destruct (negb (eqf v v') || eqb b b') eqn:e; auto. symmetry.
  apply canon_cons_inv_elem; auto. apply concat_norm; auto. 
  apply (normalized_without_head b' v'). auto.
Qed.

Theorem canon_concat_assoc {A: Type} `{Group A} (x y z: CanonFreeGroup A) : Normalized x -> 
   Normalized y -> Normalized z -> canon_concat (canon_concat x y) z = canon_concat x (canon_concat y z).
Proof.
  revert y z. induction x; intros y z Nx Ny Nz; auto. cbn. destruct a. 
  rewrite canon_concat_cons, IHx; auto.
  - apply (normalized_without_head b a). auto.
  - apply concat_norm; auto. apply (normalized_without_head b a). auto.
Qed.

Theorem cons_append_comm {A: Type} `{Group A} (b b': bool) (v v': A) (x: CanonFreeGroup A) :
  canon_cons b v (canon_append b' v' x) = canon_append b' v' (canon_cons b v x).
Proof.
  admit.
Admitted.

Theorem canon_concat_append {A: Type} `{Group A} (b: bool) (v: A) (x y: CanonFreeGroup A) :
  canon_concat x (canon_append b v y) = canon_append b v (canon_concat x y).
Proof.
  induction x; auto. cbn. destruct a. rewrite IHx. apply cons_append_comm.
Qed.

Lemma appinv_list_remaining {A: Type} `{Group A} (x y: CanonFreeGroup A) :
  canon_concat x (canon_apinv x y) = y.
Proof.
  revert y. induction x; auto. intros y. cbn. destruct a. rewrite IHx.
  cbn. rewrite eqf_refl, eqb_negb2. cbn. auto.
Qed.

Theorem canon_right_inv {A: Type} `{Group A} (x : CanonFreeGroup A) : 
  canon_concat x (canon_inv x) = [].
Proof.
  induction x; auto. cbn. destruct a. rewrite appinv_list_remaining.
  cbn. rewrite eqf_refl, eqb_negb2. cbn. auto.
Qed.

Lemma cannon_inv_concat {A: Type} `{Group A} (x y: CanonFreeGroup A) : 
  canon_apinv x y = canon_inv x ++ y.
Proof.
  unfold canon_inv. revert y. induction x; auto; intros y.
  cbn. destruct a. rewrite IHx, (IHx [(negb b, a)]), <- app_assoc.
  auto.
Qed.

Lemma cannon_inv_append {A: Type} `{Group A} (b: bool) (v: A) (x : CanonFreeGroup A) : 
  canon_inv (x ++ [(b, v)]) = (negb b, v) :: canon_inv x.
Proof.
  revert b v. induction x; auto. intros b v. cbn. destruct a.
  rewrite cannon_inv_concat, IHx, cannon_inv_concat, app_comm_cons. auto.
Qed.

Lemma append_at_end {A: Type} `{Group A} (b: bool) (v: A) (x : CanonFreeGroup A) : 
  Normalized (x ++ [(b, v)]) -> x ++ [(b, v)] = canon_append b v x.
Proof.
  revert b v. induction x; auto; intros b v H0; destruct a. cbn in *.
  destruct x.
  - cbn in *. dependent destruction H0. destruct H0.
    + rewrite <- eqf_false_iff in H0. rewrite eqf_sym, H0. auto.
    + subst. rewrite eqb_reflx, orb_true_r. auto.
  - rewrite IHx; auto. dependent destruction H0; auto.
Qed.

Lemma concat_normalized_l {A: Type} `{Group A} (x y: CanonFreeGroup A) :
  Normalized (x ++ y) -> Normalized x.
Proof.
  destruct x.
  - constructor.
  - intros H0. revert H0. revert p. induction x; intros p H0.
    + destruct p. constructor.
    + destruct p, a. constructor; dependent destruction H0; auto.
Qed.

Theorem canon_left_inv {A: Type} `{Group A} (x : CanonFreeGroup A) : 
  Normalized x -> canon_concat (canon_inv x) x = [].
Proof.
  induction x using rev_ind; auto. intros N. destruct x.
  rewrite cannon_inv_append. cbn. rewrite append_at_end; auto.
  rewrite canon_concat_append, IHx.
  - cbn. rewrite eqf_refl, eqb_negb1. auto.
  - apply (concat_normalized_l x0 [(b, a)]). auto.
Qed.



