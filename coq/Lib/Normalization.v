Require Import Lib.HoTT.
Require Import Lib.EqDec.

Definition normalzation {A: Type} (f: A -> A) :=
  forall x: A, f x = f (f x).

Class equivalance_relation {A: Type} (R: A -> A -> Prop) := equiv_proof {
  equiv_refl  : forall x: A, R x x;
  equiv_sym   : forall x y: A, R x y -> R y x;
  equiv_trans : forall x y z: A, R x y -> R y z -> R x z;
}.

Definition norm_equiv {A: Type} (f: A -> A) (x y: A) : Prop := 
  f x = f y.

Global Instance equiv_Eq {A: Type} : equivalance_relation (eq (A := A)).
Proof.
  constructor; [auto | auto| ].
  intros x y z H H'. subst. reflexivity.
Qed.

Global Instance equiv_normalization {A: Type} (f: A -> A) : 
  equivalance_relation (norm_equiv f).
Proof.
  unfold norm_equiv. constructor; [auto | auto| ].
  intros x y z H H'. rewrite H. auto.
Qed.

Record QuotientNorm {A: Type} `{E: EqDec A} (f: A -> A) `{N: normalzation f} := Quot {
  val    : A;
  normal : val = f val;
}.

Lemma norm_works {A: Type} (f: A -> A) (N: normalzation f) (x: A) : f x = f (f x).
Proof.
  apply N.
Qed.

Definition make_QN {A: Type} `{E: EqDec A} (f: A -> A) `{N: normalzation f} 
  (x: A) : QuotientNorm f (N := N) := 
{|
  val    := f x;
  normal := norm_works f N x;
|}.
  
Arguments val {_ _ _ _}.
Arguments normal {_ _ _ _}.

Theorem quotient_unique_representation (A: Type) `{E: EqDec A} (f: A -> A) 
  `{N: normalzation f} : forall x y: QuotientNorm f, 
  norm_equiv f (val x (N := N)) (val y (N := N)) -> x = y.
Proof.
  unfold norm_equiv. intros x y H. destruct x as (x & Px). destruct y as (y & Py).
  cbn in *. assert (x = y) by (rewrite Px, Py; auto). subst. f_equal.
  assert (isHSet A) by (apply dec_eq_hset; auto). auto.
Qed.