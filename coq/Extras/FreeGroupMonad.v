Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Master.Lib.Algebra.
Require Import Master.Lib.EqDec.
Require Import Master.FreeGroup.

Class Monad (M : Type -> Type) := MondadDef {
  pure       : forall {A : Type}, A -> M A;
  bind       : forall {A B : Type}, M A -> (A -> M B) -> M B;
  left_bind  : forall {A B : Type} (f: A -> M B) (x: A), bind (pure x) f = f x; 
  right_bind : forall {A B : Type} (x: M A), bind x pure = x; 
  comp_bind  : forall {A B C : Type} (f: B -> M C) (g : A -> M B) (x: M A),
                 bind (bind x g) f = bind x (fun y => bind (g y) f);
}.


(* Function definition *)
Definition quot_pure {A: Type} `{EqGroup A} (x: A) := Singl true x.

Definition naive_pure {A: Type} (x: A) := [(true, x)].

Fixpoint naive_bind {A B: Type} `{EqGroup A} `{EqGroup B} 
  (x : NaiveFreeGroup A) (f: A -> NaiveFreeGroup B) 
  : NaiveFreeGroup B :=
  match x with
  | []               => []
  | (true, v) :: x'  => naive_concat (f v) (naive_bind x' f)
  | (false, v) :: x' => 
      naive_concat (naive_inv (f v)) (naive_bind x' f)
  end.

Definition quot_bind {A B: Type} `{EqGroup A} `{EqGroup B} (x : QuotFreeGroup A)
  (f: A -> QuotFreeGroup B) : QuotFreeGroup B :=
  to_quot (naive_bind (to_naive x) (fun y => to_naive (f y))).



Theorem bind_norm {A B: Type} `{EqGroup A} `{EqGroup B} (x: NaiveFreeGroup A)
  (f: A -> NaiveFreeGroup B) : (forall a: A, Normalized (f a)) -> Normalized (naive_bind x f).
Proof.
  intros Nf. induction x as [|(b, v)]; [constructor|].
  cbn. destruct b.
  - now apply concat_norm.
  - apply concat_norm; [now apply inv_norm | auto].
Qed.

Theorem naive_bind_cons {A B: Type} `{EqGroup A} `{EqGroup B} (b: bool) (v: A) 
  (x: NaiveFreeGroup A) (f: A -> NaiveFreeGroup B) :
  (forall a: A, Normalized (f a)) -> naive_bind (naive_cons b v x) f = 
  naive_concat (if b then f v else naive_inv (f v)) (naive_bind x f).
Proof.
  intros Nf. destruct x as [| (b', v')]; cbn; [now destruct b| destruct b, b'].
  - now rewrite eqb_reflx, orb_true_r.
  - destruct (eqf v v') eqn:veq; [|auto]. rewrite <- eqf_iff in veq. subst. 
    cbn. rewrite <- naive_concat_assoc, r_naive_concat_inv; 
    [auto | auto | now apply inv_norm | now apply bind_norm].
  - destruct (eqf v v') eqn:veq; auto. rewrite <- eqf_iff in veq. subst. 
    cbn. rewrite <- naive_concat_assoc, l_naive_concat_inv; 
    [auto | auto | now apply inv_norm | auto | now apply bind_norm].
  - now rewrite eqb_reflx, orb_true_r.
Qed.

Theorem naive_bind_concat {A B: Type} `{EqGroup A} `{EqGroup B} (x y : NaiveFreeGroup A)
  (f: A -> NaiveFreeGroup B) : (forall a: A, Normalized (f a)) ->
  naive_bind (naive_concat x y) f = naive_concat (naive_bind x f) (naive_bind y f).
Proof.
  intros Nf. induction x as [| (b, v)]; [auto |]. cbn. rewrite naive_bind_cons; auto.
  destruct b.
  - rewrite IHx, naive_concat_assoc; [..| apply bind_norm | apply bind_norm ]; auto.
  - rewrite IHx, naive_concat_assoc; 
    [| apply inv_norm | apply bind_norm | apply bind_norm ]; auto.
Qed.

Lemma cons_inv_is_append {A: Type} `{EqGroup A} (b: bool) (v : A) (x: NaiveFreeGroup A) :
  Normalized x -> naive_inv (naive_cons b v x) = naive_append (negb b) v (naive_inv x).
Proof.
  intros Nx. induction x as [| (b', v')]; auto. cbn.
  destruct (negb (eqf v v') || eqb b b') eqn:e.
  - cbn. assert (Normalized (naive_inv ((b', v') :: x))) by now apply inv_norm.
    rewrite apinv_def, apinv_def, append_is_concat_at_end, 
    concat_for_normalized, <- app_assoc; auto.
    + rewrite <- app_assoc. cbn. apply rev_normalized; 
      [ now rewrite <- apinv_def | now rewrite condition_iff, eqf_sym, eqb_sym, eqb_neg_izo].
    + now rewrite <- apinv_def.
  - assert (Normalized (naive_inv ((b', v') :: x))) by now apply inv_norm.
    rewrite apinv_def,  apinv_def, append_is_concat_at_end, 
    <- (concat_for_normalized (naive_inv x) [(negb b', v')]), naive_concat_assoc.
    5-6: now rewrite <- apinv_def.
    3-4: constructor.
    + cbn. rewrite eqf_sym, eqb_sym, eqb_neg_izo, e, r_naive_concat_id, app_nil_r; auto.
      apply inv_norm. apply (normalized_without_head b' v'). auto.
    + apply inv_norm. apply (normalized_without_head b' v'). auto.
Qed.

Lemma cons_apinv_is_append {A: Type} `{EqGroup A} (b: bool) (v : A) (x: NaiveFreeGroup A) :
  Normalized x -> naive_apinv (naive_cons b v x) [] = naive_append (negb b) v (naive_apinv x []).
Proof.
  intros Nx. apply cons_inv_is_append. auto.
Qed. 

Lemma naive_concat_inv {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) :
  Normalized x -> Normalized y -> 
  naive_inv (naive_concat x y) = naive_concat (naive_inv y) (naive_inv x). 
Proof.
  unfold naive_inv. intros Nx Ny. induction x as [| (b, v)].
  - cbn. rewrite r_naive_concat_id; [| apply inv_norm]; auto.
  - cbn. assert (Normalized x) by now apply (normalized_without_head b v).
    assert (Normalized (naive_inv ((b, v) :: x))) by now apply inv_norm.
    rewrite cons_apinv_is_append, IHx, (apinv_def x [(negb b, v)]), 
    <- concat_for_normalized, append_is_concat_at_end, naive_concat_assoc;
    [| apply inv_norm | apply inv_norm | constructor | apply concat_norm;  apply inv_norm 
     | rewrite <- apinv_def | | apply concat_norm] ; auto.
Qed.

Lemma naive_concat_apinv {A: Type} `{EqGroup A} (x y: NaiveFreeGroup A) :
  Normalized x -> Normalized y -> 
  naive_apinv (naive_concat x y) [] = naive_concat (naive_apinv y []) (naive_apinv x []).
Proof. 
  intros Hx Hy. apply naive_concat_inv; auto.
Qed.

Lemma naive_bind_rev {A B: Type} `{EqGroup A} `{EqGroup B} (b: bool) (v: A)
  (x: NaiveFreeGroup A) (f: A -> NaiveFreeGroup B) : (forall a: A, Normalized (f a)) -> 
  (naive_bind (x ++ [(b, v)]) f) = naive_concat (naive_bind x f) (if b then f v else naive_inv (f v)).
Proof.
  intros Nf. induction x as [| (b', v')]; [auto|].
  - cbn. destruct b; rewrite r_naive_concat_id; auto. now apply inv_norm.
  - cbn. destruct b, b'; rewrite naive_concat_assoc, IHx; auto.
    1,3-4,7: now apply bind_norm.
    1-4: now apply inv_norm.
Qed.

Lemma concat_inv_inv {A: Type} `{EqGroup A} (x : NaiveFreeGroup A) : 
  Normalized x -> naive_inv (naive_inv x) = x.
Proof.
  intro Nx. rewrite <- (r_naive_concat_id (naive_inv (naive_inv x))),
  <- (l_naive_concat_inv x), <- (naive_concat_assoc), l_naive_concat_inv; auto.
  2,4: apply inv_norm.
  1-4: now apply inv_norm.
Qed.

Lemma concat_apinv_apinv {A: Type} `{EqGroup A} (x : NaiveFreeGroup A) : 
  Normalized x -> naive_apinv (naive_apinv x []) [] = x.
Proof.
  intro Nx. now apply concat_inv_inv.
Qed.

Theorem naive_bind_inv {A B: Type} `{EqGroup A} `{EqGroup B} (x: NaiveFreeGroup A)
  (f: A -> NaiveFreeGroup B) : (forall a: A, Normalized (f a)) -> 
  naive_inv (naive_bind x f) = (naive_bind (naive_inv x) f).
Proof.
  unfold naive_inv. intros Nf. induction x as [| (b, v)]; auto. cbn. destruct b; cbn.
  - rewrite naive_concat_apinv, IHx, (apinv_def x [(false, v)]), naive_bind_rev;
    [.. | apply bind_norm]; auto.
  - rewrite naive_concat_apinv, IHx, (apinv_def x [(true, v)]), naive_bind_rev;
    [.. | apply inv_norm | apply bind_norm]; auto. unfold naive_inv.
    rewrite concat_apinv_apinv; auto. 
Qed.

Theorem naive_comp_bind {A B C : Type} `{EqGroup A} `{EqGroup B} `{EqGroup C}
  (f: B -> NaiveFreeGroup C) (g : A -> NaiveFreeGroup B) (x: NaiveFreeGroup A) : 
  (forall b: B, Normalized (f b)) -> (forall a: A, Normalized (g a)) ->
  naive_bind (naive_bind x g) f = naive_bind x (fun y => naive_bind (g y) f).
Proof.
  intros Nf Ng. induction x as [|(b, v) x]; [auto|]. cbn. destruct b.
  - now rewrite naive_bind_concat, IHx.
  - now rewrite naive_bind_concat, IHx, <- naive_bind_inv.
Qed.

Theorem naive_left_bind {A B : Type} `{EqGroup A} `{EqGroup B} (f : A -> NaiveFreeGroup B)
  (x: A) : (forall a: A, Normalized (f a)) -> naive_bind (naive_pure x) f = f x.
Proof.
  intro Nf. cbn. now rewrite r_naive_concat_id.
Qed.

Theorem naive_right_bind {A B : Type} `{EqGroup A} `{EqGroup B} (f : A -> NaiveFreeGroup B)
  (x: NaiveFreeGroup A) : Normalized x -> naive_bind x naive_pure = x.
Proof.
  intro Nx. induction x as [| (b, v)]; [auto|]. cbn. destruct b; rewrite IHx.
  1,3: symmetry; now apply cons_for_normalized.
  - now apply (normalized_without_head true v).
  - now apply (normalized_without_head false v).
Qed.
  