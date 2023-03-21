Require Import Setoid.

Inductive NonEmpty (A: Type) : Prop := intro : A -> NonEmpty A.

Axiom axiom_of_prop_ext : forall P Q: Prop, (P <-> Q) <-> (P = Q).
Axiom axiom_of_choise : forall A: Type, NonEmpty A -> A.

Lemma nonempty_equiv (A: Type) : NonEmpty A <-> exists x: A, True.
Proof.
  split; intros H.
  - destruct H. exists X. auto.
  - admit.
Admitted.

Definition choose (A: Type) (P : A -> Prop) (h : exists x, P x) : A.
Proof.
  apply axiom_of_choise. constructor. admit.
Admitted.

Theorem em (P: Prop) : P \/ ~P.
  assert (exists x, x = (True \/ P)) by (exists (True \/ P); auto).
  assert (exists x, x = (False \/ P)) by (exists (False \/ P); auto).
Abort.

Axiom Quot : forall {A: Type}, (A -> A -> Prop) -> Type.

Axiom Quot_mk : forall {A:  Type} (r: A -> A -> Prop),
  A -> Quot r.

Axiom Quot_ind : 
  forall (A:  Type) (r: A -> A -> Prop) (P: Quot r -> Prop),
    (forall a: A, P (Quot_mk r a)) -> forall q: Quot r, P q.

Axiom Quot_lift :
  forall {A:  Type} {r: A -> A -> Prop} {B: Type} (f: A -> B),
    (forall a b: A, r a b -> f a = f b) -> Quot r -> B.

Axiom Quot_sound :
  forall (A: Type) (r: A -> A -> Prop) (a b: A),
    r a b -> Quot_mk r a = Quot_mk r b.

Theorem exists_base {A: Type} (r: A -> A -> Prop) (q: Quot r) :
  exists x, q = Quot_mk r x.
Proof.
  induction q using Quot_ind. exists a; auto.
Qed.

Axiom Quot_lift' : forall {A:  Type} {r: A -> A -> Prop} {B: Type} 
  (f: A -> B) (P: forall a b: A, r a b -> f a = f b) (x: A),
    f x = Quot_lift f P (Quot_mk r x).

Definition fun_ext_eq (A B: Type) (f g: A -> B) := forall x: A, f x = g x.

Definition ExtFun (A B: Type) := Quot (fun_ext_eq A B).

Definition id {A: Type} (x: A) := x.

Definition fun_app {A B: Type} (f: Quot (fun_ext_eq A B)) : A -> B.
Proof.
  intro x. apply (Quot_lift (fun f: A -> B => f x) (r := fun_ext_eq A B)); auto.
Defined.

Theorem fun_ext (A B: Type) (f g: A -> B): (forall x, f x = g x) -> f = g.
Proof.
  intros H.
  assert (fun_app (Quot_mk (fun_ext_eq A B) f) = fun_app (Quot_mk (fun_ext_eq A B) g)).
  { f_equal. apply Quot_sound. auto. }
  unfold fun_app in *. rewrite <- (Quot_lift' (fun f : A -> B => f x)) in H0.
  assert (forall a b: A, (fun_ext_eq A B) a b -> a = b
  rewrite id_is_id, (id_is_id (Quot_mk (fun_ext_eq A B) f)) in H0.
  rewrite Quot_lift in H0.
  assert (forall y, y = id y).
  





Axiom Quot : forall A: Type, (A -> A -> Prop) -> Type.

Axiom Quot.mk : forall (A:  Type) (r: A -> A -> Prop),
  A -> Quot r.

Axiom Quot.ind : 
  forall (A:  Type) (r: A -> A -> Prop) (P: Quot r -> Prop),
      (forall a: A, P (Quot.mk r a)) -> forall q: Quot r, P q.

Axiom Quot.lift :
  forall (A:  Type) (r: A -> A -> Prop) (B: Type) (f: A -> B),
    (forall a b: A, r a b -> f a = f b) -> Quot r -> B.

Axiom Quot.sound :
  forall (A: Type) (r: A -> A -> Prop) (a b: A),
    r a b -> Quot.mk r a = Quot.mk r b.