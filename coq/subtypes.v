Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.EqdepFacts.

Definition zero (x: nat) : Prop := x = O.

Theorem zero_subtype : forall n m: sig zero, n = m.
Proof.
  intros n m. unfold zero in *. destruct n, m. subst. reflexivity.
Qed.

Lemma one_is_not_zero: 1 <> 0.
Proof.
  intro e. inversion e.
Qed.

Lemma two_is_not_zero: 2 <> 0.
Proof.
  intro e. inversion e.
Qed.

Theorem diffrent_onne_zero : exists n m: sig (fun x => x <> 0), n <> m.
Proof.
  exists (exist _ 1 one_is_not_zero). exists (exist _ 2 two_is_not_zero). intro H.
  inversion H.
Qed.

Record sig' {A: Type} (P: A -> Prop) := {
  val : A;
  sub : P val
}.

Arguments val {A P} _.
Arguments sub {A P} _.

Definition sig_sig' {A: Type} {P: A -> Prop} (x: sig P) : sig' P :=
match x with
| exist _ v p => {| val := v ; sub := p |}
end.

Definition sig'_sig {A: Type} {P: A -> Prop} (x: sig' P) : sig P :=
exist _ (val x) (sub x).

Theorem sig_id : forall A: Type, forall P: A -> Prop, forall x: sig P, sig'_sig (sig_sig' x) = x.
Proof.
  intros A P x. destruct x. unfold sig'_sig. cbn. reflexivity.
Qed.

Theorem sig'_id : forall A: Type, forall P: A -> Prop, forall x: sig' P, sig_sig' (sig'_sig x) = x.
Proof.
  intros A P x. destruct x. cbn. reflexivity.
Qed.

Definition not_K : Prop := exists A: Type, exists x y: A, exists p q: x = y, p <> q.

Definition K {A: Type} (x y: A) (p q: x = y): Prop := p = q.


Lemma eq_JMeq : forall (A: Type) (x y: A), x = y -> x ~= y.
Proof.
  intros A x y H. rewrite H. trivial.
Qed.

Lemma not_eq_JMeq : forall (A: Type) (x y: A), x <> y -> x ~= y -> False.
Proof.
  intros A x y H H0. apply H. apply (JMeq_ind (fun z => z = y) eq_refl). apply JMeq_sym. assumption.
Qed.

Print Assumptions   JMeq_eq_dep_id.

Theorem not_unique_sigT : not_K -> exists (A: Type) (P: A -> Type) (x y: sigT P),
  projT1 x = projT1 y /\ x <> y.
Proof.
  unfold not_K.
  intros (A & x & y & p & q & H).
  exists A. exists (fun y => x = y). exists (existT _ y p), (existT _ y q).
  split.
  - cbn. reflexivity.
  - intro e. assert (eq_dep A (eq x) y p y q).
    + apply eq_sigT_eq_dep. assumption.
    + assert (p ~= q) by (apply eq_dep_JMeq; assumption). subst. apply H.  trivial.
Qed.
Print Assumptions  not_unique_sigT.



Theorem irrelevance_unique_sig : (forall (P: Prop) (x y: P), x = y) -> forall (A: Type) (P: A -> Prop) (x y: {z: A| P z}),
  proj1_sig x = proj1_sig y -> x = y.
Proof.
  intros K A P [x_v x_p] [y_v y_p] H. cbn in H. subst. apply eq_dep_eq_sig.
  specialize (K (P y_v) x_p y_p). subst. constructor.
Qed.


Class izo (A B: Type) := izo_def {
  f   : A -> B;
  inv : B -> A;
  id1 : forall a: A, inv (f a) = a;
  id2 : forall b: B, f (inv b) = b;
}.

Theorem sig_izo_sigT (A: Type) (P: A -> Prop) : izo {x : A | P x} {y : A & {x : A | P x}}.
Proof.
  apply izo_def.




Definition Eq_dep_eq_on {U: Type} (P : U -> Type) (p : U) (x : P p) :=
    forall (y : P p), eq_dep U P p x p y -> x = y.

Definition Eq_dep_eq := forall (U: Type) (P : U -> Type) (p : U) (x : P p), Eq_dep_eq_on P p x.

Definition UIP_on_ {U: Type} (x y : U) (p1 : x = y) :=
    forall (p2 : x = y), p1 = p2.

Definition UIP_ := forall (U: Type) (x y : U) (p1 : x = y), UIP_on_ x y p1.


Lemma eq_dep_eq_on__UIP_on (U: Type) (x y : U) (p1 : x = y) :
    Eq_dep_eq_on (fun y => x = y) x eq_refl -> UIP_on_ x y p1.
Proof.
  intro eq_dep_eq. red. destruct p1. intros p2. apply eq_dep_eq. destruct p2. constructor.
Qed.

Lemma eq_dep_eq__UIP : Eq_dep_eq -> UIP_.
Proof.
  intros eq_dep_eq U x y p1. destruct p1. intros p2. apply eq_dep_eq. destruct p2. constructor.
Qed.

Lemma UIP_eq_dep_eq_ : UIP_ -> Eq_dep_eq.
Proof.
  intros uip U P p x y H. unfold UIP_ in uip. unfold UIP_on_ in uip. dependent destruction H.
Qed.


