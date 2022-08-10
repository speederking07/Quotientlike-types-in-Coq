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

Theorem norm_unique {A: Type} `{choosable A} (R: A -> A -> bool) `{equivalance_relation A R} (x y: A) :
  R x y = true -> norm R x = norm R y.
Proof.
  intro. unfold norm. unfold equiv_exists.