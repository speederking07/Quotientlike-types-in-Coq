(* https://www2.mathematik.tu-darmstadt.de/~streicher/HabilStreicher.pdf *)


Inductive eq_dep (U : Type) (P : U -> Type) (p : U) (x : P p) : forall q : U, P q -> Prop :=
    eq_dep_intro : eq_dep U P p x p x.

Inductive eq_dep1 (U : Type) (P : U -> Type) (p:U) (x:P p) (q:U) (y:P q) : Prop :=
  eq_dep1_intro : forall h:q = p, x = eq_rect q P y p h -> eq_dep1 U P p x q y.


Lemma eq_dep_dep1 :
  forall (U : Type) (P : U -> Type) (p q:U) (x:P p) (y:P q), eq_dep U P p x q y -> eq_dep1 U P p x q y.
Proof.
  destruct 1. apply (eq_dep1_intro U P p x p x eq_refl). cbn. reflexivity.
Qed.


Definition Eq_rect_eq :=
  forall (U: Type) (p:U) (P:U -> Type) (x:P p) (h:p = p), x = eq_rect p P x p h.

Definition Eq_dep_eq :=
  forall (U: Type) (P:U->Type) (p:U) (x y:P p), eq_dep U P p x p y -> x = y.

Definition SigT_eq :=
  forall (U: Type) (P:U->Type) (p:U) (x y:P p), existT P p x = existT P p y -> x = y.

Definition UIP :=
  forall (U: Type) (x y:U) (p1 p2:x = y), p1 = p2.

Definition Streicher_K :=
  forall (U: Type) (x:U) (P:x = x -> Prop), P (refl_equal x) -> forall p:x = x, P p.


Lemma SigT_eq_dep : forall (U: Type) (P: U -> Type) (p q:U) (x:P p) (y:P q),
  existT P p x = existT P q y -> eq_dep U P p x q y.
Proof.
  intros.
  dependent rewrite H.
  apply eq_dep_intro.
Qed.

Lemma Eq_deo_sigT : forall (U:Type) (P:U -> Type) (p q:U) (x:P p) (y:P q),
  eq_dep U P p x q y -> existT P p x = existT P q y.
Proof.
  destruct 1. reflexivity.
Qed.


Lemma Eq_dep_eq_SigT_eq : Eq_dep_eq -> SigT_eq.
Proof.
  intros eq_dep_eq U x y p1 p2 H. apply eq_dep_eq. apply SigT_eq_dep. assumption.
Qed.

Lemma SigT_eq_eq__UIP : SigT_eq -> UIP.
Proof.
  intros eq_dep_eq U x y p1. destruct p1. intros p2. apply eq_dep_eq. destruct p2. constructor.
Qed.

Lemma UIP_Streicher_K : UIP -> Streicher_K.
Proof.
  intros uip U x P H p. unfold UIP in *. destruct (uip U x x p eq_refl). assumption.
Qed.

Lemma Streicher_K_Eq_rect_eq : Streicher_K -> Eq_rect_eq.
Proof.
  intros K U p P x h. apply K with (p := h). cbn. reflexivity.
Qed.

Lemma Eq_rect_eq_Eq_dep_eq : Eq_rect_eq -> Eq_dep_eq.
Proof.
  intros eq_rect_eq. red. intros. assert (H0: eq_dep1 U P p x p y) by (apply eq_dep_dep1; assumption).
  destruct H0. rewrite <- eq_rect_eq in H0. assumption.
Qed.
