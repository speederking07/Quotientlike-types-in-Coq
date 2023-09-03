Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import StrictProp.
Import ListNotations.

Require Import Master.Lib.Algebra.
Require Import Master.Lib.Normalization.
Require Import Master.Lib.EqDec.


Class EqGroup (A : Type) `{E: EqDec A} `{G: Group A} := {}.

Global Instance EqGroup_def {A: Type} `{E: EqDec A} `{G: Group A} : EqGroup A.
Proof.
Qed.

Definition NaiveFreeGroup (A: Type) := list (bool*A).

Fixpoint normalize {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) :=
match x with
| [] => []
| (b, v) :: x' => 
    match normalize x' with
    | [] => [(b, v)]
    | (b', v') :: x'' => if andb (eqf v v') (xorb b b')
                         then x''
                         else (b, v) :: (b', v') :: x''
    end
end.

Inductive Normalized {A: Type} : NaiveFreeGroup A -> Prop :=
| NNil   : Normalized []
| NSingl : forall (b : bool) (v : A), Normalized [(b, v)]
| NCons  : forall (b b': bool) (v v' : A) (x: NaiveFreeGroup A), 
            v <> v' \/ b = b' -> Normalized ((b', v') :: x) ->
            Normalized ((b, v) :: (b', v') :: x).



Inductive NEQuotFreeGroup (A: Type) `{EqGroup A} :=
| Singl  : bool -> A -> NEQuotFreeGroup A
| Switch : forall x: A, Squash (x <> zero) -> NEQuotFreeGroup A -> NEQuotFreeGroup A
| Stay   : A -> NEQuotFreeGroup A -> NEQuotFreeGroup A.

Arguments Switch {A E G H}.
Arguments Stay {A E G H}.
Arguments Singl {A E G H}.

Definition QuotFreeGroup (A: Type) `{EqGroup A} := option (NEQuotFreeGroup A).

Fixpoint to_quot' {A: Type} `{EqGroup A} (b : bool) (v: A) (x: NaiveFreeGroup A) : NEQuotFreeGroup A :=
match x with 
| []             => Singl b v
| (b', v') :: x' => if eqb b b' 
                      then Stay (sub v v') (to_quot' b' v' x')
                      else match eqf_leibniz (sub v v') zero with
                           | ReflectF _ p => Switch (sub v v') (squash p) (to_quot' b' v' x')
                           | _  => (Singl b v) (* invalid *)
                           end
end.

Definition to_quot {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) : QuotFreeGroup A :=
match x with
| [] => None
| (b, v) :: x' => Some (to_quot' b v x')
end.

Definition all_to_quot {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) : QuotFreeGroup A :=
to_quot (normalize x).

Fixpoint to_naive' {A: Type} `{EqGroup A} (x: NEQuotFreeGroup A) : bool * A * list (bool*A) :=
match x with 
| Singl b v     => ((b, v), [])
| Stay v x'     => match to_naive' x' with
                   | ((b, v'), y)  => ((b, op v v'), (b, v') :: y)
                   end
| Switch v _ x' => match to_naive' x' with
                   | ((b, v'), y)  => ((negb b, op v v'), (b, v') :: y)
                   end
end.

Definition to_naive {A: Type} `{EqGroup A} (x: QuotFreeGroup A) : NaiveFreeGroup A :=
match x with
| None => []
| Some x' => let (h, t) := to_naive' x' in h :: t
end.



(* Ancilary lemmas *)
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

Lemma group_squash_non_zero {A: Type} `{EqGroup A} (x : A) : Squash (x <> zero) -> x <> zero.
Proof.
  intros H0. destruct (eqf_leibniz x zero); auto. subst. apply (squash_not_refl zero). auto.
Qed.

Lemma eqf_sub_not_zero {A: Type} `{EqGroup A} (x y: A) : sub x y <> zero <-> eqf x y = false.
Proof.
  unfold sub. split.
  - intros H0. destruct (eqf_leibniz x y); [|auto]. subst. rewrite r_op_inv in H0. 
    contradiction.
  - intros H0 H1. assert (x = y) by (apply sub_zero_uniq; auto). subst.
    rewrite eqf_refl in H0. discriminate.
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

Lemma condition_iff {A: Type} `{EqGroup A} (b b': bool) (v v': A) :
  v <> v' \/ b = b' <-> negb (eqf v v') || eqb b b' = true.
Proof.
  split.
  - intros [|].
    + rewrite not_eqf_iff in H0. rewrite H0. auto.
    + subst. rewrite eqb_reflx, orb_true_r. auto.
  - intro H0. rewrite orb_true_iff, negb_true_iff in H0. destruct H0.
    + left. rewrite not_eqf_iff. auto.
    + right. apply eqb_prop. auto.
Qed.

Lemma condition_iff' {A: Type} `{EqGroup A} (b b': bool) (v v': A) :
  v <> v' \/ b = b' <-> eqf v v' && xorb b b' = false.
Proof.
  split.
  - intros [|].
    + rewrite not_eqf_iff in H0. rewrite H0. auto.
    + subst. rewrite xorb_nilpotent, andb_false_r. auto.
  - intro H0. rewrite andb_false_iff in H0. destruct H0.
    + left. rewrite not_eqf_iff. auto.
    + right. apply xorb_eq. auto.
Qed.


Lemma condition_false_iff {A: Type} `{EqGroup A} (b b': bool) (v v': A) :
  v = v' /\ b = negb b' <-> negb (eqf v v') || eqb b b' = false.
Proof.
  split.
  - intros []. subst. rewrite eqf_refl, eqb_negb1. auto.
  - intro H0. rewrite orb_false_iff, negb_false_iff in H0. destruct H0. split.
    + rewrite eqf_iff. auto.
    + destruct b, b'; auto; cbn in *; try discriminate.
Qed.


Lemma eqb_neg_izo (x y : bool) : eqb (negb x) (negb y) = eqb x y.
Proof.
  destruct x, y; auto.
Qed.


(* normalization lemmas *)

Lemma normalized_without_head {A: Type} `{EqGroup A} (b: bool) (v: A) (x: NaiveFreeGroup A) :
  Normalized ((b, v) :: x) -> Normalized x.
Proof.
  intros Nx. destruct x; [constructor|].
  destruct p as (b', v'). now dependent destruction Nx.
Qed.

Lemma concat_normalized_l {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) :
  Normalized (x ++ y) -> Normalized x.
Proof.
  destruct x as [| (b, v)]; [constructor|].
  revert b v. induction x as [| (b', v')]; intros b v H0; [constructor|].
  dependent destruction H0. constructor; auto.
Qed.

Lemma concat_normalized_r {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) :
  Normalized (x ++ y) -> Normalized y.
Proof.
  induction x as [| (b, v)]; [auto|].
  intros H0. apply IHx. rewrite <- app_comm_cons in H0.
  now apply (normalized_without_head b v).
Qed.

Theorem normalize_normalizes {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) :
  Normalized (normalize x).
Proof.
  induction x as [|(b & v) x]; [constructor | ].
  cbn in *. destruct (normalize x) as [|(b' & v') x']; [constructor|].
  destruct (eqf v v' && xorb b b') eqn:e.
  - now apply (normalized_without_head b' v').
  - constructor; [|auto]. now apply condition_iff'.
Qed.

Theorem normalize_is_id_for_normalized {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) :
  Normalized x -> normalize x = x.
Proof.
  intros Nx. induction Nx; [auto | auto |]. rewrite condition_iff' in H0.
  cbn in *. destruct (normalize x) as [| (b'' & v'') l].
  - now rewrite H0, IHNx.
  - now rewrite IHNx, H0.  
Qed.

Theorem normalize_idempotent {A: Type} `{EqGroup A} :
  normalzation normalize.
Proof.
  intros x. symmetry. apply normalize_is_id_for_normalized.
  apply normalize_normalizes.
Qed.




(* to_quot and to_naive lemmas *)
Theorem quot_epi_naive {A: Type} `{EqGroup A} (x: QuotFreeGroup A) : 
  to_quot (to_naive x) = x.
Proof.
  destruct x as [x |]; auto. induction x; [auto|..]; cbn in *.
  - destruct (to_naive' x0) as [[b  v] l]. cbn in *. 
    inversion IHx. subst. rewrite eqb_negb1, sub_op. 
    destruct (eqf_leibniz x zero); [|auto]. subst. now apply (squash_not_refl zero).
  - destruct (to_naive' x) as [[b  v] l]. cbn in *.
    inversion IHx. subst. now rewrite eqb_reflx, sub_op.
Qed.

Theorem naive_epi_quot {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) : 
  Normalized x -> to_naive (to_quot x) = x.
Proof.
  intros N. induction N; [auto | auto |]. cbn in *. destruct H0 as [v_neq | b_neq].
  - destruct (eqb b b') eqn:b_eq.
    + cbn. destruct (to_naive' (to_quot' b' v' x)) as [[b'' v''] l]. 
      inversion IHN. subst. rewrite op_sub. f_equal. f_equal. symmetry. 
      now apply eqb_prop.
    + destruct (eqf_leibniz (sub v v') zero).
      * assert (v = v') by (apply sub_zero_uniq; auto). contradiction.
      * cbn. destruct (to_naive' (to_quot' b' v' x)) as [[b'' v''] l]. 
        inversion IHN; subst. rewrite op_sub. f_equal. f_equal. symmetry. 
        now apply not_eqb_is_neg.
  - subst. rewrite eqb_reflx. cbn. destruct (to_naive' (to_quot' b' v' x)) as [[b'' v''] l]. 
    inversion IHN; subst. now rewrite op_sub.
Qed.

Lemma to_naive_not_nil {A: Type} `{EqGroup A} (x: NEQuotFreeGroup A) : to_naive (Some x) <> nil.
Proof.
  intros H0. destruct x; cbn in *; [inversion H0|..].
  - destruct (to_naive' x0) as [[b v] l]. inversion H0.
  - destruct (to_naive' x) as [[b v] l]. inversion H0.
Qed.

Theorem quot_is_normal {A: Type} `{EqGroup A} (x: QuotFreeGroup A) : Normalized (to_naive x).
Proof.
  destruct x as [x |]; cbn; [|constructor]. induction x.
  - cbn. constructor.
  - dependent destruction IHx; cbn in *.
    + assert (to_naive (Some x0) <> []) by (apply to_naive_not_nil). rewrite x in H0.
      contradiction.
    + destruct (to_naive' x0) as [[b' v'] l]. inversion x; subst.
      constructor; constructor. apply add_is_non_zero. apply group_squash_non_zero. auto.
    + destruct (to_naive' x0) as [[b'' v''] l]. inversion x; subst. constructor.
      * left. apply add_is_non_zero. now apply group_squash_non_zero.
      * now constructor.
  - dependent destruction IHx; cbn in *.
    + assert (to_naive (Some x0) <> []) by (apply to_naive_not_nil). rewrite x in H0.
      contradiction.
    + destruct (to_naive' x0) as [[b' v'] l]. inversion x; subst. 
      constructor; [right|]; constructor.
    + destruct (to_naive' x1) as [[b'' v''] l]. inversion x; subst. 
      constructor; [right|]; now constructor.
Qed.




(* Naive concat definition *)

Definition naive_cons {A: Type} `{EqGroup A} (b: bool) (v: A) (x: NaiveFreeGroup A) :
  NaiveFreeGroup A :=
  match x with
  | [] => [(b, v)]
  | (b', v') :: t => if negb (eqf v v') || eqb b b'
                     then (b, v) :: (b', v') :: t
                     else t
  end.

Fixpoint naive_concat {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) : NaiveFreeGroup A :=
  match x with
  | []           => y
  | (b, v) :: x' => naive_cons b v (naive_concat x' y)
  end.

Theorem concat_norm {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) : 
  Normalized x -> Normalized y -> Normalized (naive_concat x y).
Proof.
  intros Nx Ny. induction Nx; [auto | ..]; cbn.
  - destruct Ny; unfold naive_cons.
    + constructor.
    + destruct (negb (eqf v v0) || eqb b b0 ) eqn:e; constructor;
      [now rewrite orb_true_iff, eqb_true_iff, negb_true_iff, <-not_eqf_iff in e | constructor].
    + destruct (negb (eqf v v0) || eqb b b0) eqn:e; auto. constructor;
      [now rewrite orb_true_iff, eqb_true_iff, negb_true_iff, <-not_eqf_iff in e | now constructor].
  - assert (negb (eqf v v') || eqb b b' = true) by
    now rewrite orb_true_iff, eqb_true_iff, negb_true_iff, <-not_eqf_iff.
    destruct (naive_concat x y) as [|(b'' & v'') l] eqn:c; unfold naive_cons in *.
    + rewrite H1. constructor; [auto | constructor].
    + cbn in *. rewrite c in *. unfold naive_cons in *. 
      destruct (negb (eqf v' v'') || eqb b' b'') eqn:e.
      * assert (negb (eqf v v') || eqb b b' = true) by
        now rewrite orb_true_iff, eqb_true_iff, negb_true_iff, <-not_eqf_iff.
        rewrite H2. constructor; auto.
      * cbn in *. destruct c; try constructor. destruct l as [| (b''' & v''')]; [constructor|]. 
        destruct (negb (eqf v v''') || eqb b b''') eqn:e1.
        -- constructor; [now rewrite orb_true_iff, eqb_true_iff, negb_true_iff, <-not_eqf_iff in e1 | auto].
        -- dependent destruction IHNx; [constructor | auto].
Qed.




(* Quot concat homomorphism *)
Fixpoint quot_hd' {A: Type} `{EqGroup A} (x: NEQuotFreeGroup A) : bool * A :=
  match x with 
  | Singl b v => (b, v)
  | Stay v x' => let (b', v') := quot_hd' x' in (b', op v v')
  | Switch v _ x' => let (b', v') := quot_hd' x' in (negb b', op v v')
  end.

Definition fq_tail' {A: Type} `{EqGroup A} (x: NEQuotFreeGroup A) : QuotFreeGroup A :=
  match x with 
  | Singl _ _     => None
  | Stay _ x'     => Some x'
  | Switch _ _ x' => Some x'
  end.

Definition quot_cons' {A: Type} `{EqGroup A} (b: bool) (v: A) (x: NEQuotFreeGroup A) : 
   QuotFreeGroup A :=
    let (b', v') := quot_hd' x in 
      if eqb b b'
      then Some (Stay (sub v v') x)
      else match eqf_leibniz (sub v v') zero with
           | ReflectT _ _ => fq_tail' x
           | ReflectF _ p => Some (Switch (sub v v') (squash p) x)
           end.

Definition quot_cons {A: Type} `{EqGroup A} (b: bool) (v: A) (x: QuotFreeGroup A) : QuotFreeGroup A :=
  match x with
  | None => Some (Singl b v)
  | Some x' => quot_cons' b v x'
  end.

Definition quot_cons2 {A: Type} `{EqGroup A} (p: bool * A) (x: QuotFreeGroup A) : QuotFreeGroup A := 
  let (b, v) := p in quot_cons b v x.

Fixpoint quot_concat' {A: Type} `{EqGroup A} (x: NEQuotFreeGroup A) 
  (y: QuotFreeGroup A) : QuotFreeGroup A :=
  match x with
  | Singl b v     => quot_cons b v y
  | Stay _ x'     => quot_cons2 (quot_hd' x) (quot_concat' x' y)
  | Switch _ _ x' => quot_cons2 (quot_hd' x) (quot_concat' x' y)
  end.

Definition quot_concat {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : QuotFreeGroup A :=
  match x with
  | None => y
  | Some x' => quot_concat' x' y
  end.

Theorem quot_naive_hd {A: Type} `{EqGroup A} (x: NEQuotFreeGroup A) :
  Some (quot_hd' x) = hd_error (to_naive (Some x)).
Proof.
  induction x; [auto|..].
  - cbn in *. destruct (to_naive' x0) as [[b v] l] eqn:e.
    cbn in *. inversion IHx. now rewrite H1.
  - cbn in *. destruct (to_naive' x) as [[b v] l] eqn:e.
    cbn in *. inversion IHx. now rewrite H1.
Qed.

Theorem quot_naive_cons_homomorphism {A: Type} `{EqGroup A} (b: bool) (v: A) (x: QuotFreeGroup A) :
  to_naive (quot_cons b v x) = naive_cons b v (to_naive x).
Proof.
  destruct x as [x |]; auto. unfold naive_cons. destruct x as [b' v' | v' p x' | v' x'].
  - cbn. destruct (eqb b b') eqn:e.
    + cbn. rewrite orb_true_r, op_sub. f_equal. f_equal. symmetry. now apply eqb_prop.
    + destruct (eqf_leibniz (sub v v') zero).
      * assert (v = v') by now apply sub_zero_uniq. subst.
        rewrite eqf_refl. auto.
      * cbn. rewrite eqf_sub_not_zero in n. rewrite n, op_sub. cbn. f_equal. f_equal.
        assert (negb b' = b) by (symmetry; now apply not_eqb_is_neg). auto. 
  - cbn. destruct (to_naive' x') as [[b'' v''] l] eqn:c.
    unfold quot_cons'. cbn. assert (hd_eq : quot_hd' x' = (b'', v'')).
    { apply some_eq. rewrite quot_naive_hd. cbn. now rewrite c. }
    rewrite hd_eq. destruct (eqb b (negb b'')) eqn:eb.
    + cbn. rewrite eqb_true_iff in eb; subst. now rewrite orb_true_r, c, op_sub. 
    + destruct (eqf_leibniz (sub v (op v' v''))).
      * assert (v = (op v' v'')) by (apply sub_zero_uniq; auto). subst.
        cbn. now rewrite eqf_refl, c.
      * cbn. rewrite eqf_sub_not_zero in n. rewrite n, c. unfold sub. cbn.
        rewrite (op_assoc  v (inv (op v' v''))), l_op_inv, r_op_id, negb_involutive.
        f_equal. rewrite eqb_not_neg in eb. subst. auto.
  - cbn. destruct (to_naive' x') as [[b'' v''] l] eqn:c.
    unfold quot_cons'. cbn. assert (hd_eq : quot_hd' x' = (b'', v'')).
    { apply some_eq. rewrite quot_naive_hd. cbn. now rewrite c. }
    rewrite hd_eq. destruct (eqb b b'') eqn:eb.
    + cbn. rewrite eqb_true_iff in eb; subst. now rewrite orb_true_r, c, op_sub. 
    + destruct (eqf_leibniz (sub v (op v' v''))).
      * assert (v = (op v' v'')) by (apply sub_zero_uniq; auto). subst.
        cbn. now rewrite eqf_refl, c.
      * cbn. rewrite eqf_sub_not_zero in n. rewrite n, c. unfold sub. cbn.
        rewrite (op_assoc  v (inv (op v' v''))), l_op_inv, r_op_id.
        f_equal. assert (b = negb b'') by (apply not_eqb_is_neg; auto).
        subst. auto.
Qed.

Theorem quot_naive_concat_homomorphism {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) :
  to_naive (quot_concat x y) = naive_concat (to_naive x) (to_naive y).
Proof.
  destruct x as [x |]; [|auto]. cbn. induction x as [b' v' | v' p x' | v' x']; cbn.
  - apply quot_naive_cons_homomorphism.
  - destruct (to_naive' x') as [[b v] l] eqn:c.
    assert (hd_eq : quot_hd' x' = (b, v)).
    { apply some_eq. rewrite quot_naive_hd. cbn. now rewrite c. }
    rewrite hd_eq. cbn in *. rewrite <- IHx'. apply quot_naive_cons_homomorphism.
  - destruct (to_naive' x') as [[b v] l] eqn:c.
    assert (hd_eq : quot_hd' x' = (b, v)).
    { apply some_eq. rewrite quot_naive_hd. cbn. now rewrite c. }
    rewrite hd_eq. cbn in *. rewrite <- IHx'. apply quot_naive_cons_homomorphism.
Qed.





(* Naive concat laws *)
Fixpoint naive_apinv {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) :=
  match x with
  | [] => y
  | (b, v) :: x' => naive_apinv x' ((negb b, v) :: y)
  end.

Definition naive_inv {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) := naive_apinv x [].

Fixpoint naive_append {A: Type} `{EqGroup A} (b: bool) (v: A) (x: NaiveFreeGroup A) :=
  match x with
  | [] => [(b, v)]
  | [(b', v')] => if negb (eqf v v') || eqb b b'
                     then [(b', v'); (b, v)]
                     else []
  | h :: x' => h :: (naive_append b v x')
  end.

Lemma append_for_normalized {A: Type} `{EqGroup A} (b: bool) (v: A) (x : NaiveFreeGroup A) : 
  Normalized (x ++ [(b, v)]) -> x ++ [(b, v)] = naive_append b v x.
Proof.
  induction x as [|(b' & v')]; [auto|..]; intros H0. cbn in *.
  destruct x as [| (b'' & v'')].
  - cbn in *. dependent destruction H0. destruct H0.
    + rewrite not_eqf_iff in H0. rewrite eqf_sym, H0. auto.
    + subst. now  rewrite eqb_reflx, orb_true_r.
  - rewrite IHx; auto. dependent destruction H0; auto.
Qed.

Lemma cons_for_normalized {A: Type} `{EqGroup A} (b: bool) (v: A) (x : NaiveFreeGroup A) : 
  Normalized ((b, v) :: x) -> (b, v) :: x = naive_cons b v x.
Proof.
  intros Nx. destruct x as [| (b' & v')]; auto. cbn. dependent destruction Nx.
  rewrite condition_iff in H0. now rewrite H0.
Qed.

Lemma naive_cons_inv_elem {A: Type} `{EqGroup A} (b b': bool) (v v': A) (x: NaiveFreeGroup A) :
  Normalized x -> negb (eqf v v') || eqb b b' = false -> naive_cons b v (naive_cons b' v' x) = x.
Proof.
  intros Nx H0. induction Nx as [| b'' v'' | b'' b''' v'' v'''].
  - cbn. rewrite H0. auto.
  - cbn. destruct (negb (eqf v' v'') || eqb b' b'') eqn:H1.
    + cbn. now rewrite H0.
    + cbn. rewrite orb_false_iff, negb_false_iff in H0, H1. destruct H0, H1.
      rewrite <-eqf_iff in H0. rewrite <-eqf_iff in H1. subst. f_equal. f_equal.
      apply eqb_false_chain with (y := b'); auto.
  - rewrite condition_iff in H1. cbn. destruct (negb (eqf v' v'') || eqb b' b'') eqn:H2.
    + cbn. rewrite H0. auto.
    + cbn in *. rewrite <- condition_false_iff in H0, H2.
      destruct H0, H2. subst. rewrite negb_involutive, H1. auto.
Qed.

Lemma naive_concat_cons {A: Type} `{EqGroup A} (b: bool) (v: A) (x y: NaiveFreeGroup A) :
  Normalized x -> Normalized y -> naive_concat (naive_cons b v x) y  = naive_cons b v (naive_concat x y).
Proof.
  intros Nx Ny. destruct x as [| (b' & v') x']; auto. cbn. 
  destruct (negb (eqf v v') || eqb b b') eqn:e; auto. symmetry.
  apply naive_cons_inv_elem; auto. apply concat_norm; auto. 
  apply (normalized_without_head b' v'). auto.
Qed.

Theorem naive_concat_assoc {A: Type} `{EqGroup A} (x y z: NaiveFreeGroup A) : Normalized x -> 
   Normalized y -> Normalized z -> naive_concat (naive_concat x y) z = naive_concat x (naive_concat y z).
Proof.
  revert y z. induction x; intros y z Nx Ny Nz; auto. cbn. destruct a. 
  rewrite naive_concat_cons, IHx; auto.
  - apply (normalized_without_head b a). auto.
  - apply concat_norm; auto. apply (normalized_without_head b a). auto.
Qed.

Lemma normalized_head {A: Type} `{EqGroup A} (b: bool) (v: A) (x: NaiveFreeGroup A) :
  hd_error x = None \/ (exists (b' : bool) (v' : A), hd_error x = Some (b', v') /\ (v <> v' \/ b = b'))
   -> Normalized x -> Normalized ((b, v) :: x).
Proof.
  intros H0 Nx. destruct x as [| (b'' & v'')]; constructor; [|auto].
  destruct H0.
  - cbn in H0. inversion H0.
  - cbn in H0. destruct H0 as [b' (v' & (H0 & H1))]. inversion H0. subst. auto.
Qed.
  

Lemma noramlized_singl_append {A: Type} `{EqGroup A} (b0 b1 b': bool) (v0 v1 v': A) (x: NaiveFreeGroup A) :
  Normalized ((b0, v0) :: (b1, v1) :: x) -> naive_concat ((b0, v0) :: (b1, v1) :: x) [(b', v')] 
  = (b0, v0) :: naive_concat ((b1, v1) :: x) [(b', v')].
Proof.
  revert b0 b1 v0 v1. induction x as [| (b2 & v2)]; intros b0 b1 v0 v1 Nx; cbn in *. 
  - dependent destruction Nx. destruct ( negb (eqf v1 v') || eqb b1 b') eqn:e; [|auto].
    cbn. rewrite condition_iff in H0. now rewrite H0.
  - dependent destruction Nx. rewrite IHx; [|auto]. rewrite condition_iff in H0.
    cbn. now rewrite H0.
Qed.

Lemma append_is_concat_at_end {A: Type} `{EqGroup A} (b: bool) (v: A) (x: NaiveFreeGroup A) :
  Normalized x -> naive_append b v x = naive_concat x [(b, v)].
Proof.
  intros Nx. revert b v. induction Nx as [| b' v' | b' b'' v' v'']; auto; intros b v.
  - cbn. now rewrite eqf_sym, eqb_sym.
  - rewrite noramlized_singl_append. 
    + cbn in *. rewrite IHNx; auto.
    + constructor; auto.
Qed.

Lemma cons_is_concat_at_start {A: Type} `{EqGroup A} (b: bool) (v: A) (x: NaiveFreeGroup A) :
  naive_cons b v x = naive_concat [(b, v)] x.
Proof.
  auto.
Qed.

Theorem cons_append_comm {A: Type} `{EqGroup A} (b b': bool) (v v': A) (x: NaiveFreeGroup A) :
  Normalized x -> naive_cons b v (naive_append b' v' x) = naive_append b' v' (naive_cons b v x).
Proof.
  intros Nx. rewrite cons_is_concat_at_start, cons_is_concat_at_start,
  append_is_concat_at_end, append_is_concat_at_end, naive_concat_assoc; auto.
  - constructor.
  - constructor.
  - apply concat_norm; [constructor | auto].
Qed.

Theorem concat_append {A: Type} `{EqGroup A} (b: bool) (v: A) (x y: NaiveFreeGroup A) :
  Normalized x -> Normalized y -> 
  naive_concat x (naive_append b v y) = naive_append b v (naive_concat x y).
Proof.
  induction x as [|(b' & v')]; [auto|]. intros Nx Ny. cbn. rewrite IHx; 
  [| now apply (normalized_without_head b' v') |auto]. apply cons_append_comm.
  apply concat_norm; auto. apply (normalized_without_head b' v'); auto.
Qed.

Lemma appinv_concat_elim {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) :
  naive_concat x (naive_apinv x y) = y.
Proof.
  revert y. induction x as [| (b & v)]; [auto|]. intros y. cbn. rewrite IHx.
  cbn. rewrite eqf_refl, eqb_negb2. auto.
Qed.

Theorem r_naive_concat_inv {A: Type} `{EqGroup A} (x : NaiveFreeGroup A) : 
  naive_concat x (naive_inv x) = [].
Proof.
  induction x as [| (b & v)]; [auto|]. cbn. rewrite appinv_concat_elim.
  cbn. rewrite eqf_refl, eqb_negb2. auto.
Qed.

Lemma apinv_def {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) : 
  naive_apinv x y = naive_inv x ++ y.
Proof.
  unfold naive_inv. revert y. induction x as [| (b & v)]; [auto|]. intros y.
  cbn. now rewrite IHx, (IHx [(negb b, v)]), <- app_assoc.
Qed.

Lemma cannon_inv_append {A: Type} `{EqGroup A} (b: bool) (v: A) (x : NaiveFreeGroup A) : 
  naive_inv (x ++ [(b, v)]) = (negb b, v) :: naive_inv x.
Proof.
  revert b v. induction x as [| (b' & v')]; [auto|]. intros b v. cbn.
  now rewrite apinv_def, IHx, apinv_def, app_comm_cons.
Qed.

Lemma concat_for_normalized {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) :
  Normalized (x ++ y) -> naive_concat x y = x ++ y.
Proof.
  intro N. induction x as [| (b, v)]; auto. cbn. 
  rewrite IHx, cons_for_normalized; auto. apply (normalized_without_head b v). 
  rewrite app_comm_cons. auto. 
Qed.

Lemma normalized_list_concat {A: Type} `{EqGroup A} (b b': bool) (v v': A) (x y: NaiveFreeGroup A) :
  Normalized (x ++ [(b, v)]) -> Normalized ((b', v') :: y) ->
  v <> v' \/ b = b' -> Normalized (x ++ (b, v) :: (b', v') :: y).
Proof.
  revert b b' v v' y. induction x using rev_ind; intros b b' v v' y Nx Ny H0.
  - cbn. constructor; auto.
  - rewrite <- app_assoc. cbn. destruct x as (b'', v''). apply IHx.
    + now apply (concat_normalized_l (x0 ++ [(b'', v'')]) [(b, v)]).
    + constructor; auto.
    + assert (Normalized [(b'', v''); (b, v)]) by
      (apply (concat_normalized_r x0); now rewrite <- app_assoc in Nx).
      dependent destruction H1. auto.
Qed. 

Theorem rev_normalized {A: Type} `{EqGroup A} (b b': bool) (v v': A) (x: NaiveFreeGroup A) :
  Normalized (x ++ [(b, v)]) -> v <> v' \/ b = b' -> Normalized (x ++ [(b, v); (b', v')]).
Proof.
  revert b b' v v'. destruct x as [| (b'', v'')] using rev_ind ; intros b b' v v' Nx H0.
  - cbn. constructor; [auto | constructor].
  - apply normalized_list_concat; [auto | constructor | auto].
Qed. 

Theorem inv_norm {A: Type} `{EqGroup A} (x: NaiveFreeGroup A) : 
  Normalized x -> Normalized (naive_inv x).
Proof.
  intros Nx. induction Nx; cbn in *; [constructor | constructor |].
  rewrite apinv_def in IHNx. rewrite apinv_def.
  apply rev_normalized; auto. destruct H0; auto. subst. auto.
Qed.

Theorem l_naive_concat_inv {A: Type} `{EqGroup A} (x : NaiveFreeGroup A) : 
  Normalized x -> naive_concat (naive_inv x) x = [].
Proof.
  induction x as [| (b & v)] using rev_ind; [auto|]. intros N.
  rewrite cannon_inv_append. cbn. rewrite append_for_normalized; auto.
  assert (Normalized x) by now apply (concat_normalized_l x [(b, v)]).
  rewrite concat_append, IHx; auto.
  - cbn. rewrite eqf_refl, eqb_negb1. auto.
  - apply inv_norm; auto.
Qed.

Theorem l_naive_concat_id {A: Type} `{EqGroup A} (x : NaiveFreeGroup A) : 
  naive_concat [] x = x.
Proof.
  auto.
Qed.

Theorem r_naive_concat_id {A: Type} `{EqGroup A} (x : NaiveFreeGroup A) : 
  Normalized x -> naive_concat x [] = x.
Proof.
  intros Nx. induction x as [| (b, v)]; [auto|]. cbn. rewrite IHx, cons_for_normalized; auto.
  apply (normalized_without_head b v); auto.
Qed.





(* Free Group is Group *)
Definition quot_zero {A: Type} `{EqGroup A} := None (A := NEQuotFreeGroup A).

Definition quot_via_naive_concat {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : QuotFreeGroup A :=
  to_quot (naive_concat (to_naive x) (to_naive y)).

Definition quot_via_naive_inv {A: Type} `{EqGroup A} (x: QuotFreeGroup A) : QuotFreeGroup A :=
  to_quot (naive_inv (to_naive x)).

Theorem l_quot_via_naive_concat_inv {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : 
  quot_via_naive_concat (quot_via_naive_inv x) x = quot_zero.
Proof.
  unfold quot_via_naive_concat, quot_via_naive_inv. rewrite naive_epi_quot.
  - rewrite l_naive_concat_inv; auto. apply quot_is_normal.
  - apply inv_norm. apply quot_is_normal.
Qed.

Theorem r_quot_via_naive_concat_inv {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : 
  quot_via_naive_concat x (quot_via_naive_inv x) = quot_zero.
Proof.
  unfold quot_via_naive_concat, quot_via_naive_inv. rewrite naive_epi_quot.
  - rewrite r_naive_concat_inv; auto.
  - apply inv_norm. apply quot_is_normal.
Qed.

Theorem l_quot_via_naive_concat_id {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : 
  quot_via_naive_concat quot_zero x = x.
Proof.
  unfold quot_via_naive_concat. cbn. apply quot_epi_naive.
Qed.

Theorem r_quot_via_naive_concat_id {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : 
  quot_via_naive_concat x quot_zero = x.
Proof.
  unfold quot_via_naive_concat. cbn. rewrite r_naive_concat_id.
  - apply quot_epi_naive.
  - apply quot_is_normal.
Qed.

Theorem quot_via_naive_concat_assoc {A: Type} `{EqGroup A} (x y z: QuotFreeGroup A) : 
  quot_via_naive_concat (quot_via_naive_concat x y) z = quot_via_naive_concat x (quot_via_naive_concat y z).
Proof.
  unfold quot_via_naive_concat. rewrite naive_epi_quot, naive_epi_quot.
  - rewrite naive_concat_assoc; auto; try apply quot_is_normal.
  - apply concat_norm; apply quot_is_normal.
  - apply concat_norm; apply quot_is_normal.
Qed.

Global Program Instance QuotFreeGroup_is_Group {A: Type} `{EqGroup A} : Group (QuotFreeGroup A) := {
  zero      := None;
  op        := quot_via_naive_concat;
  inv       := quot_via_naive_inv;
}.

Next Obligation. now apply l_quot_via_naive_concat_id. Defined.
Next Obligation. now apply r_quot_via_naive_concat_id. Defined.
Next Obligation. now apply l_quot_via_naive_concat_inv. Defined.
Next Obligation. now apply r_quot_via_naive_concat_inv. Defined.
Next Obligation. now apply quot_via_naive_concat_assoc. Defined.

(* Free Group eqdec *)

Fixpoint quot_eq' {A: Type} `{EqGroup A} (x y: NEQuotFreeGroup A) : bool :=
  match x, y with
  | Singl xb xv,    Singl yb yv    => eqb xb yb && eqf xv yv
  | Switch xr _ x', Switch yr _ y' => eqf xr yr && quot_eq' x' y'
  | Stay xr x',     Stay yr y'     => eqf xr yr && quot_eq' x' y'
  | _,              _              => false
  end.

Definition quot_eq {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : bool :=
  match x, y with
  | None,    None    => true
  | Some x', Some y' => quot_eq' x' y'
  | _,       _       => false
  end.

Theorem quot_eqf_eq {A: Type} `{EqGroup A} (x y: QuotFreeGroup A) : reflect (x = y) (quot_eq x y).
Proof.
  apply iff_reflect. split.
  - intros []. destruct x as [x |]; auto. induction x;  cbn in *. 
    + now rewrite eqb_reflx, eqf_refl.
    + now rewrite eqf_refl, IHx.
    + now rewrite eqf_refl, IHx.
  - intros H0. destruct x as [x |]; destruct y as [y |]; cbn in *; [| inversion H0 | inversion H0 | auto].
    f_equal. revert H0. revert y. induction x; intros y H0.
    + destruct y; cbn in *; [| inversion H0 | inversion H0]. 
      rewrite andb_true_iff in H0; destruct H0. rewrite eqb_true_iff in H0.
      rewrite <-eqf_iff in H1. subst. auto.
    + destruct y; cbn in *; [inversion H0 | | inversion H0]. rewrite andb_true_iff in H0.
      destruct H0. rewrite <-eqf_iff in H0. specialize (IHx y H1). subst. auto.
    + destruct y; cbn in *; [inversion H0| inversion H0 |]. rewrite andb_true_iff in H0.
      destruct H0. rewrite <-eqf_iff in H0. specialize (IHx y H1). subst. auto.
Qed.


Global Program Instance QuotFreeGroup_is_EqDec {A: Type} `{EqGroup A} : EqDec (QuotFreeGroup A) := {
  eqf       := quot_eq;
}.

Next Obligation. apply quot_eqf_eq; auto. Defined.


(* Exotic Integers *)
Definition FreeGroupIntegrals := QuotFreeGroup unit.

