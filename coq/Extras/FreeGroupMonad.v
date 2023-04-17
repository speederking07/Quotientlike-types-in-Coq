Require Import Coq.Program.Equality.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Lib.Algebra.
Require Import Lib.EqDec.
Require Import FreeGroup.

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

Definition canon_pure {A: Type} (x: A) := [(true, x)].

Fixpoint canon_bind {A B: Type} `{EqGroup A} `{EqGroup B} (x : CanonFreeGroup A)
  (f: A -> CanonFreeGroup B) : CanonFreeGroup B :=
  match x with
  | [] => []
  | (b, v) :: x' => if b
                    then canon_concat (f v) (canon_bind x' f)
                    else canon_concat (canon_inv (f v)) (canon_bind x' f)
  end.

Definition quot_bind {A B: Type} `{EqGroup A} `{EqGroup B} (x : QuotFreeGroup A)
  (f: A -> QuotFreeGroup B) : QuotFreeGroup B :=
  to_quot (canon_bind (to_canon x) (fun y => to_canon (f y))).



Theorem bind_norm {A B: Type} `{EqGroup A} `{EqGroup B} (x: CanonFreeGroup A)
  (f: A -> CanonFreeGroup B) : (forall a: A, Normalized (f a)) -> Normalized (canon_bind x f).
Proof.
  intros Nf. induction x as [|(b, v)]; [constructor|].
  cbn. destruct b.
  - now apply concat_norm.
  - apply concat_norm; [now apply inv_norm | auto].
Qed.

Theorem canon_bind_cons {A B: Type} `{EqGroup A} `{EqGroup B} (b: bool) (v: A) 
  (x: CanonFreeGroup A) (f: A -> CanonFreeGroup B) :
  (forall a: A, Normalized (f a)) -> canon_bind (canon_cons b v x) f = 
  canon_concat (if b then f v else canon_inv (f v)) (canon_bind x f).
Proof.
  intros Nf. destruct x as [| (b', v')]; cbn; [now destruct b| destruct b, b'].
  - now rewrite eqb_reflx, orb_true_r.
  - destruct (eqf v v') eqn:veq; [|auto]. rewrite <-eqf_iff in veq. subst. 
    cbn. rewrite <- canon_concat_assoc, r_canon_concat_inv; 
    [auto | auto | now apply inv_norm | now apply bind_norm].
  - destruct (eqf v v') eqn:veq; auto. rewrite <-eqf_iff in veq. subst. 
    cbn. rewrite <- canon_concat_assoc, l_canon_concat_inv; 
    [auto | auto | now apply inv_norm | auto | now apply bind_norm].
  - now rewrite eqb_reflx, orb_true_r.
Qed.

Theorem canon_bind_concat {A B: Type} `{EqGroup A} `{EqGroup B} (x y : CanonFreeGroup A)
  (f: A -> CanonFreeGroup B) : (forall a: A, Normalized (f a)) ->
  canon_bind (canon_concat x y) f = canon_concat (canon_bind x f) (canon_bind y f).
Proof.
  intros Nf. induction x as [| (b, v)]; [auto |]. cbn. rewrite canon_bind_cons; auto.
  destruct b.
  - rewrite IHx, canon_concat_assoc; [..| apply bind_norm | apply bind_norm ]; auto.
  - rewrite IHx, canon_concat_assoc; 
    [| apply inv_norm | apply bind_norm | apply bind_norm ]; auto.
Qed.

Lemma cons_inv_is_append {A: Type} `{EqGroup A} (b: bool) (v : A) (x: CanonFreeGroup A) :
  Normalized x -> canon_inv (canon_cons b v x) = canon_append (negb b) v (canon_inv x).
Proof.
  intros Nx. induction x as [| (b', v')]; auto. cbn.
  destruct (negb (eqf v v') || eqb b b') eqn:e.
  - cbn. assert (Normalized (canon_inv ((b', v') :: x))) by now apply inv_norm.
    rewrite apinv_def, apinv_def, append_is_concat_at_end, 
    concat_for_normalized, <- app_assoc; auto.
    + rewrite <- app_assoc. cbn. apply rev_normalized; 
      [ now rewrite <- apinv_def | now rewrite condition_iff, eqf_sym, eqb_sym, eqb_neg_izo].
    + now rewrite <- apinv_def.
  - assert (Normalized (canon_inv ((b', v') :: x))) by now apply inv_norm.
    rewrite apinv_def,  apinv_def, append_is_concat_at_end, 
    <- (concat_for_normalized (canon_inv x) [(negb b', v')]), canon_concat_assoc.
    5-6: now rewrite <- apinv_def.
    3-4: constructor.
    + cbn. rewrite eqf_sym, eqb_sym, eqb_neg_izo, e, r_canon_concat_id, app_nil_r; auto.
      apply inv_norm. apply (normalized_without_head b' v'). auto.
    + apply inv_norm. apply (normalized_without_head b' v'). auto.
Qed.

Lemma cons_apinv_is_append {A: Type} `{EqGroup A} (b: bool) (v : A) (x: CanonFreeGroup A) :
  Normalized x -> canon_apinv (canon_cons b v x) [] = canon_append (negb b) v (canon_apinv x []).
Proof.
  intros Nx. apply cons_inv_is_append. auto.
Qed. 

Lemma canon_concat_inv {A: Type} `{EqGroup A} (x y: CanonFreeGroup A) :
  Normalized x -> Normalized y -> 
  canon_inv (canon_concat x y) = canon_concat (canon_inv y) (canon_inv x). 
Proof.
  unfold canon_inv. intros Nx Ny. induction x as [| (b, v)].
  - cbn. rewrite r_canon_concat_id; [| apply inv_norm]; auto.
  - cbn. assert (Normalized x) by now apply (normalized_without_head b v).
    assert (Normalized (canon_inv ((b, v) :: x))) by now apply inv_norm.
    rewrite cons_apinv_is_append, IHx, (apinv_def x [(negb b, v)]), 
    <- concat_for_normalized, append_is_concat_at_end, canon_concat_assoc;
    [| apply inv_norm | apply inv_norm | constructor | apply concat_norm;  apply inv_norm 
     | rewrite <- apinv_def | | apply concat_norm] ; auto.
Qed.

Lemma canon_concat_apinv {A: Type} `{EqGroup A} (x y: CanonFreeGroup A) :
  Normalized x -> Normalized y -> 
  canon_apinv (canon_concat x y) [] = canon_concat (canon_apinv y []) (canon_apinv x []).
Proof. 
  intros Hx Hy. apply canon_concat_inv; auto.
Qed.

Lemma canon_bind_rev {A B: Type} `{EqGroup A} `{EqGroup B} (b: bool) (v: A)
  (x: CanonFreeGroup A) (f: A -> CanonFreeGroup B) : (forall a: A, Normalized (f a)) -> 
  (canon_bind (x ++ [(b, v)]) f) = canon_concat (canon_bind x f) (if b then f v else canon_inv (f v)).
Proof.
  intros Nf. induction x as [| (b', v')]; [auto|].
  - cbn. destruct b; rewrite r_canon_concat_id; auto. now apply inv_norm.
  - cbn. destruct b, b'; rewrite canon_concat_assoc, IHx; auto.
    1,3-4,7: now apply bind_norm.
    1-4: now apply inv_norm.
Qed.

Lemma concat_inv_inv {A: Type} `{EqGroup A} (x : CanonFreeGroup A) : 
  Normalized x -> canon_inv (canon_inv x) = x.
Proof.
  intro Nx. rewrite <- (r_canon_concat_id (canon_inv (canon_inv x))), <- (l_canon_concat_inv x),
  <- (canon_concat_assoc), l_canon_concat_inv; auto.
  2,4: apply inv_norm.
  1-4: now apply inv_norm.
Qed.

Lemma concat_apinv_apinv {A: Type} `{EqGroup A} (x : CanonFreeGroup A) : 
  Normalized x -> canon_apinv (canon_apinv x []) [] = x.
Proof.
  intro Nx. now apply concat_inv_inv.
Qed.

Theorem canon_bind_inv {A B: Type} `{EqGroup A} `{EqGroup B} (x: CanonFreeGroup A)
  (f: A -> CanonFreeGroup B) : (forall a: A, Normalized (f a)) -> 
  canon_inv (canon_bind x f) = (canon_bind (canon_inv x) f).
Proof.
  unfold canon_inv. intros Nf. induction x as [| (b, v)]; auto. cbn. destruct b; cbn.
  - rewrite canon_concat_apinv, IHx, (apinv_def x [(false, v)]), canon_bind_rev;
    [.. | apply bind_norm]; auto.
  - rewrite canon_concat_apinv, IHx, (apinv_def x [(true, v)]), canon_bind_rev;
    [.. | apply inv_norm | apply bind_norm]; auto. unfold canon_inv.
    rewrite concat_apinv_apinv; auto. 
Qed.

Theorem canon_comp_bind {A B C : Type} `{EqGroup A} `{EqGroup B} `{EqGroup C}
  (f: B -> CanonFreeGroup C) (g : A -> CanonFreeGroup B) (x: CanonFreeGroup A) : 
  (forall b: B, Normalized (f b)) -> (forall a: A, Normalized (g a)) ->
  canon_bind (canon_bind x g) f = canon_bind x (fun y => canon_bind (g y) f).
Proof.
  intros Nf Ng. induction x as [|(b, v) x]; [auto|]. cbn. destruct b.
  - now rewrite canon_bind_concat, IHx.
  - now rewrite canon_bind_concat, IHx, <- canon_bind_inv.
Qed.

Theorem canon_left_bind {A B : Type} `{EqGroup A} `{EqGroup B} (f : A -> CanonFreeGroup B)
  (x: A) : (forall a: A, Normalized (f a)) -> canon_bind (canon_pure x) f = f x.
Proof.
  intro Nf. cbn. now rewrite r_canon_concat_id.
Qed.

Theorem canon_right_bind {A B : Type} `{EqGroup A} `{EqGroup B} (f : A -> CanonFreeGroup B)
  (x: CanonFreeGroup A) : Normalized x -> canon_bind x canon_pure = x.
Proof.
  intro Nx. induction x as [| (b, v)]; [auto|]. cbn. destruct b; rewrite IHx.
  1,3: symmetry; now apply cons_for_normalized.
  - now apply (normalized_without_head true v).
  - now apply (normalized_without_head false v).
Qed.
  