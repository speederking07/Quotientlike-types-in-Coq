Require Import Setoid.

Class equivalance_relation {A: Type} (R: A -> A -> bool) := {
  equiv_refl : forall x: A, R x x = true;
  equiv_sym : forall x y: A, R x y = true -> R y x = true;
  equiv_trans : forall x y z: A, R x y = true -> R y z = true -> R x z = true;
}.

Class choosable {A: Type} :=
  xchoose : forall P: A -> bool, (exists x: A, P x = true) -> A.

Lemma equiv_exists {A: Type} (x: A) (R: A -> A -> bool) `{equivalance_relation A R} : exists y, R x y = true.
Proof. exists x. apply equiv_refl. Defined.

Definition norm {A: Type} `{choosable A} (R: A -> A -> bool) `{equivalance_relation A R} (x : A) :=
 xchoose (R x) (equiv_exists x R).

Definition EqExt {A B: Type} (f g: A -> B) := forall x: A, f x = g x.

Lemma eq_ext_for_app : 
  (forall (A B C: Type) (f : (A -> B) -> C) (g h: A -> B), EqExt g h -> (f g) = (f h)) <-> 
  (forall (A B: Type) (f g: A -> B), EqExt f g -> f = g).
Proof.
  unfold EqExt. split.
  - intros H A B f g eq_ext. specialize (H A B (A -> B) (fun x => x) f g eq_ext).
    cbn in H. assumption.
  - intros H A B C f g h eq_ext. f_equal. apply H. assumption.
Qed.

Lemma eq_ext_app_fun : 
  (forall (A B C: Type) (f : (A -> B) -> C) (g h: A -> B), EqExt g h -> (f g) = (f h)) <-> 
  (forall (A B C D: Type) (f : (A -> B) -> C -> D) (g h: A -> B), EqExt g h -> EqExt (f g) (f h)).
Proof.
  unfold EqExt. split.
  - intros H A B C D f g h ext x. rewrite eq_ext_for_app in H. f_equal. apply H.
    assumption.
  - intros H A B C f g h ext. specialize (H A B unit C). 
    specialize (H (fun t _ => f t) g h ext tt). cbn in H. assumption.
Qed.


Theorem norm_unique {A: Type} `{choosable A} (R: A -> A -> bool) `{equivalance_relation A R} (x y: A) :
  R x y = true -> norm R x = norm R y.
Proof.
  intro. unfold norm. unfold equiv_exists. 