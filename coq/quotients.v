Require Import StrictProp.
Require Import Setoid.

Lemma Spr1_inj {A P} {a b : @Ssig A P} (e : Spr1 a = Spr1 b) : a = b.
Proof.
  destruct a, b. cbn in e. subst. reflexivity.
Qed.

(* To jest nasza funkcja kanalizująca*)

Definition normalzation {A: Type} (f: A -> A) :=
  forall x: A, f x = f (f x).

Inductive Seq {A: Type} : A -> A -> SProp :=
| srefl : forall x: A, Seq x x.


Definition Squotient {A: Type} {f: A->A} (N: normalzation f) : Type :=
  Ssig (fun x : A => Seq x (f x)).

Class equivalance_relation {A: Type} (R: A -> A -> Prop) := equiv_proof {
  equiv_refl  : forall x: A, R x x;
  equiv_sym   : forall x y: A, R x y -> R y x;
  equiv_trans : forall x y z: A, R x y -> R y z -> R x z;
}.

Definition norm_equiv {A: Type} (f: A -> A) (N: normalzation f) (x y: A) : Prop :=
  f x = f y.

Theorem norm_equiv_is_equivalance_relation (A: Type) (f: A -> A) (N: normalzation f)
  : equivalance_relation (norm_equiv f N).
Proof.
  unfold norm_equiv. apply equiv_proof.
  - intro x. reflexivity.
  - intros x y H. symmetry. assumption.
  - intros x y z H H0. destruct H, H0. reflexivity.
Qed. 

Print Ssig.


Theorem only_one_repersentant {A: Type} (f: A -> A) (N: normalzation f) 
  (q q': Squotient N) : norm_equiv f N (Spr1 q) (Spr1 q') -> Seq q q'.
Proof.
  intro H. 
  destruct q, q'. cbn in *. 
  assert (E: Seq Spr1 Spr0).
  - unfold norm_equiv in H. destruct Spr2, Spr3.
    subst. constructor.
  - destruct E. constructor.
Qed.

Check only_one_repersentant.





(* Możemy skorzystać zamiast tego z funkcji określającej czy coś jest w postaci normalnej *)
(* Ale do stworzenia takiej funckji porzebowalibyśmy rozstrzygalenj równości na type A
    albo wyłączonego środka  *)

(* From HoTT *) 

Inductive Empty : Type := .
Notation "! f" := (f -> Empty) (at level 75). 
Notation "p ^" := (eq_sym p) (at level 30). 
Notation "f @ g" := (eq_trans f g) (at level 40).

Class Decidable (A : Type) :=
  dec : A + (!A).
Arguments dec A {_}.

Definition DecidablePath (A : Type) :=
  forall x y: A, Decidable (x = y).

Class EqDec (A : Type) := { 
  eqf : A -> A -> bool ;
  eqf_leibniz : forall x y, eqf x y = true <-> x = y
}.

Class HSet (X : Type) := 
  hSet : forall (x y : X) (p q : x = y), p = q.

Class WeaklyConstant {A B: Type} (f : A -> B) :=
  wconst : forall x y, f x = f y.

Class Collapsible (A : Type) :={ 
  collapse : A -> A ;
  wconst_collapse : WeaklyConstant collapse
}.

Theorem dec_means_collaps : forall A : Type, Decidable A -> Collapsible A.
Proof.
  intros A eq. destruct eq.
  - exists (fun x => a). unfold WeaklyConstant. intros x y. reflexivity.
  - exists (fun x => x). unfold WeaklyConstant. intros x y. assert Empty by auto. destruct H.
Qed.

Class PathCollapsible (A : Type) :=
  path_coll : forall (x y : A), Collapsible (x = y).

Theorem eq_dec_means_collapsible : forall A : Type, DecidablePath A -> PathCollapsible A.
Proof.
  intros A dec x y. apply dec_means_collaps. specialize (dec x y). assumption.
Qed.

Lemma loop_eq : forall A: Type, forall x y: A, forall p: x = y, 
  eq_refl = (p ^) @ p.
Proof.
  intros A x y []. cbn. reflexivity.
Qed.

Theorem pathcoll_means_hset (A : Type) : PathCollapsible A -> HSet A.
Proof.
  unfold HSet. intros H x y. unfold PathCollapsible in *.
  assert (h: forall e: x=y, e = ((collapse (eq_refl x)) ^) @ (collapse e)).
  - intros []. apply loop_eq.
  - intros p q. rewrite (h q), (h p), (wconst_collapse p q). reflexivity.
Qed.

Theorem pathdec_hset (A: Type) : DecidablePath A -> HSet A.
Proof.
  intros H. apply pathcoll_means_hset. apply eq_dec_means_collapsible. assumption.
Qed.

Theorem eqDec_pathdec : forall A: Type, EqDec A -> DecidablePath A.
Proof.
  intros A H x y. destruct H. case_eq (eqf0 x y).
  - intro H1. left. apply (eqf_leibniz0 x y). assumption.
  - intro H1. right. intro H2. rewrite <- (eqf_leibniz0 x y) in H2. rewrite H1 in H2.
    discriminate.
Qed.

Theorem dec_eq_hset : forall A: Type, EqDec A -> HSet A.
Proof.
  intros A H. apply pathdec_hset. apply eqDec_pathdec. assumption.
Qed.

Theorem bool_hset : HSet bool.
Proof.
  apply dec_eq_hset. exists (fun x y: bool => (if x then y else (if y then false else true))).
  intros x y. destruct x, y; split; intro H; auto.
Qed.

Definition id {A: Type} (x: A) := x.

(* End HoTT *)

Definition get_norm_check {A: Type} (E: EqDec A) {f: A -> A} (N: normalzation f) (x: A) 
  : bool := eqf x (f x).

Record quotient' {A: Type} (E: EqDec A) {f: A->A} (N: normalzation f)  := {
  val': A;
  proof': get_norm_check E N val' = true
}.

Arguments val' {A _ _ _} _.
Arguments proof' {A _ _ _} _.


Theorem only_one_repersentant' {A: Type} (E: EqDec A) (f: A -> A) (N: normalzation f)
  : forall q q': (quotient' E N), norm_equiv f N (val' q) (val' q') -> q = q'.
Proof.
  intros q q' H. unfold norm_equiv in H. destruct q, q'. cbn in *. assert (val'0 = val'1).
  - unfold get_norm_check in *. rewrite eqf_leibniz in proof'0, proof'1.
    destruct proof'0, proof'1, H. reflexivity.
  - assert (HSet: HSet bool) by apply bool_hset. subst. assert (proof'0 = proof'1).
    + specialize (HSet (get_norm_check E N val'1) true). apply HSet.
    + subst. reflexivity.
Qed.


(* From Pragmatic Quotints types *)
Record quot_class_of (T Q : Type) := QuotClass {
  repr : Q -> T;
  pi : T -> Q;
  reprK : forall x : Q, pi (repr x) = x
}.

Record quotType (T : Type) := QuotType {
  quot_sort :> Type; 
  quot_class : quot_class_of T quot_sort
}.

Theorem quotient'_is_quotType {A: Type} (E: EqDec A) {f: A->A} (N: normalzation f) : quotType A.
Proof.
  exists (quotient' E N).
  - exists val' f. intro x.

