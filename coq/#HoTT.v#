Require Import Setoid.

Inductive Empty : Type := .


Definition dot {A B C} (f: B -> C) (g: A -> B) := fun (x: A) => f (g x).

Notation "f $ g" := (dot f g) (at level 75). 
Notation "! f" := (f -> Empty) (at level 75). 
Notation "p ^" := (eq_sym p) (at level 30). 
Notation "f @ g" := (eq_trans f g) (at level 40). 

Class Decidable (A : Type) :=
  dec : A + (!A).
Arguments dec A {_}.

Definition DecidablePath (A : Type) :=
  forall x y: A, Decidable (x = y).

Class Contr (A: Type) := {
  center : A;
  contr : forall x: A, x = center
}.

Class HProp (P : Type) :=
  hProp : forall p q : P, p = q.

Class HSet (X : Type) := 
  hSet : forall (x y : X) (p q : x = y), p = q.

Class EqDec (A : Type) := { 
  eqf : A -> A -> bool ;
  eqf_leibniz : forall x y, eqf x y = true <-> x = y
}.

(*   _ : forall x y, reflect (x = y) (eqf x y)
Require Import Bool.
Print reflect.
 *)
Class WeaklyConstant {A B: Type} (f : A -> B) :=
  wconst : forall x y, f x = f y.

Class Collapsible (A : Type) :={ 
  collapse : A -> A ;
  wconst_collapse : WeaklyConstant collapse
}.

Theorem map_tought_HProp : forall A B P: Type, forall f: A -> P, forall g: P -> B,
  HProp P -> WeaklyConstant (g $ f).
Proof.
  intros A B P f g HProp. unfold WeaklyConstant. intros x y. unfold dot. assert (f x = f y).
  - destruct (HProp  (f x) (f y)). reflexivity.
  - destruct H. reflexivity.
Qed.

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

Lemma loop_eq' : forall A: Type, forall x y: A, forall p: x = y, 
  eq_refl = p @ (p ^).
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

Definition isLeft {A B: Type} (x : A + B): bool :=
  match x with
  | inl _ => true
  | _ => false
  end.

Theorem pathdec_eqDec : forall A: Type, DecidablePath A -> EqDec A.
Proof.
  intros A H. unfold DecidablePath in H. exists (fun x y => isLeft (H x y)).
  intros x y. split.
  - case_eq (H x y); intros p H1.
    + intros _. assumption.
    + cbn. intro H2. discriminate.
  - intro H1. subst. case_eq (H y y); intros p H1.
    + cbn. reflexivity.
    + assert Empty by auto. contradiction.
Qed.

Theorem dec_eq_hset : forall A: Type, EqDec A -> HSet A.
Proof.
  intros A H. apply pathdec_hset. apply eqDec_pathdec. assumption.
Qed.

Definition path_contr {A: Type} `{Contr A} (x y: A) : x = y :=
 (contr x) @ ((contr y)^).

Lemma all_path_eq_in_contr {A: Type} `{Contr A} {x y: A}: forall p q: x = y, p = q.
Proof.
  intros p q. assert (forall e: x = y, e = path_contr x y).
  - intros []. unfold path_contr. unfold contr. destruct H. apply loop_eq'.
  - rewrite (H0 p). rewrite (H0 q). reflexivity.
Qed.

Lemma contr_bottom (A: Type) `{Contr A} (x y: A): Contr (x = y).
Proof.
  exists (path_contr x y).
  intros p. apply all_path_eq_in_contr.
Qed.

Theorem contr_is_hprop (A: Type) `{Contr A} : HProp A.
Proof.
  unfold HProp. intros p q. destruct H. rewrite contr0.
  specialize (contr0 p). rewrite contr0. reflexivity.
Qed.

Theorem contr_not_eq_hprop : exists A: Type, HProp A /\ (! Contr A).
Proof.
  exists Empty. split.
  - unfold HProp. intros [] _.
  - intros []. destruct center0.
Qed. 

Lemma all_path_eq_in_hprop {A: Type} `{HProp A} {x y: A}: forall p q: x = y, p = q.
Proof.
  intros p q. assert (HProp (x=y)).
  - apply contr_is_hprop. apply contr_bottom. exists x. intro z. apply H.
  - apply H0. 
Qed.

Theorem hprop_def (A: Type) `{HProp A} (x y: A) : Contr (x = y).
Proof.
  exists (H x y). intro p. apply all_path_eq_in_hprop.
Qed.

Theorem hprop_inv (A: Type) `{Contr A} (x y: A) : HProp (x = y).
Proof.
  apply contr_is_hprop. apply contr_bottom. assumption.
Qed.

Theorem hprop_is_hset (A: Type) `{HProp A} : HSet A.
Proof.
  unfold HSet. intros x y p q. apply all_path_eq_in_hprop.
Qed.

Theorem hprop_not_eq_hset : exists A: Type, HSet A /\ !HProp A.
Proof.
  exists bool. split.
  - apply pathdec_hset. intros x y. unfold Decidable. 
    destruct x, y; auto; right; intro H; discriminate.
  - intro H. specialize (H true false). discriminate.
Qed.

Theorem hset_def {A: Type} `{HSet A} (x y: A) : HProp (x = y).
Proof.
  unfold HProp. apply H.
Qed. 

Theorem paths_between_paths_are_eq_in_hset {A: Type} `{HSet A} {x y: A} {a b: x = y}:
 forall p q: a = b, p = q.
Proof.
  intros p q. assert (Contr (p = q)). 
  - unfold HSet in H. apply contr_bottom. apply contr_bottom. exists a. intro c. apply H.
  - destruct H0. assumption.
Qed. 

Theorem hset_inv {A: Type} `{HProp A} (x y: A) : HSet (x = y).
Proof.
  intros a b p q. assert (HSet A) by (apply hprop_is_hset; assumption).
  apply paths_between_paths_are_eq_in_hset.
Qed.

Definition id {A: Type} (x: A) := x.

Definition ap {A B: Type} {x y: A} (f: A -> B) (p: x = y): f x = f y :=
  match p with
  | eq_refl => eq_refl
  end.

Definition transport {A: Type} {x y: A} {P: A -> Type} (p: x = y) : P x -> P y :=
  match p with
  | eq_refl => id
  end.

Notation "p *" := (transport p) (at level 20). 

Definition apd {A: Type} {x y: A} {P: A -> Type} (f: forall x:A, P x) (p: x = y) : 
  (p *) (f x) = f y :=
  match p with
  | eq_refl => eq_refl
  end.

(* ap proofs *)

Theorem ap_distr {A B: Type} {x y z: A} (f: A -> B) (p: x = y) (q: y = z)
  : ap f (p @ q) = (ap f p) @ (ap f q).
Proof.
  destruct p, q. cbn. reflexivity.
Qed.

Theorem ap_inv {A B: Type} {x y: A} (f: A -> B) (p: x = y) : ap f (p ^) = (ap f p) ^.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Theorem ap_conn {A B C: Type} {x y: A} (f: A -> B) (g: B -> C) (p: x = y)
  : ap g (ap f p) = ap (g $ f) p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Theorem ap_id {A B: Type} {x y: A} (p: x = y) : ap id p = p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

(* transport proofs *)

Theorem transport_dist {A: Type} {P: A -> Type} {x y z: A} (p: x = y) (q: y = z) (u: P x)
  : (q *) ((p *) u) = ((p @ q) *) u.
Proof.
  destruct p, q. cbn. reflexivity.
Qed.

Theorem transport_ap {A B: Type} {P: B -> Type} {x y: A} (f: A -> B) (p: x = y) (u: P (f x))
  : transport (P := P $ f) p u = transport (ap f p) u.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Theorem transport_fun {A: Type} {P Q: A -> Type} {x y: A} (f: forall x, P x -> Q x) (p: x = y)
  (u: P x) : transport (P := Q) p (f x u) = f y (transport (P := P) p u).
Proof.
  destruct p. cbn. reflexivity.
Qed.


Theorem dep_pair_eq : forall (A: Type) (P: A -> Type) (x y: A) (p: P x) (q: P y),
  existT P x p = existT P y q -> exists e: x = y, transport e p = q.
Proof.
  intros A P x y p q H. inversion H. exists eq_refl. cbn. trivial. Show Proof. 
Qed.

Theorem dep_pair_eq_inv : forall (A: Type) (P: A -> Type) (x y: A) (p: P x) (q: P y),
   (exists e: x = y, transport e p = q) -> existT P x p = existT P y q.
Proof.
  intros A P x y p q (-> & []). cbn. reflexivity. Show Proof. 
Qed.


Definition pointwise_paths {A B: Type}  (f g : A -> B)
  := forall x, f x = g x.

Notation "f == g" := (pointwise_paths f g) (at level 100).

Class IsEquiv {A B : Type} (f : A -> B) := {
  equiv_inv : B -> A ;
  eisretr : (f $ equiv_inv) == id ;
  eissect : (equiv_inv $ f) == id ;
  eisadj : forall x : A, eisretr (f x) = ap f (eissect x) ;
}.

Arguments IsEquiv {A B}.

Class IsEquiv' {A B : Type} (f : A -> B) := {
  equiv_inv_A : B -> A ;
  equiv_inv_B : B -> A ;
  equiv_id_A : f $ equiv_inv_A == id ;
  equiv_id_B : equiv_inv_B $ f == id ;
}.

Class IsEquiv'' {A B : Type} (f : A -> B) := 
  contr_equiv : forall y: B, Contr(exists x, f x = y).


Theorem equiv_same (A B: Type) (f: A -> B) `{IsEquiv A B f} : IsEquiv' f.
Proof.
  destruct H. exists equiv_inv0 equiv_inv0; assumption.
Qed.

Theorem equiv_same' (A B: Type) (f: A -> B) `{IsEquiv' A B f} : IsEquiv f.
Proof.
  destruct H.
Abort.

Record Equiv A B := {
  equiv_fun : A -> B ;
  equiv_isequiv : IsEquiv equiv_fun
}.
  

Notation "A <~> B" := (Equiv A B) (at level 120).

Check (fun x => equiv_inv (equiv_fun x)).

Theorem hprop_from_hset_eq (A: Type) `{HSet A} (P: A -> Prop) (f: A -> A)
  (H0: forall x, x = f x <~> P x) (x: A) : HProp (P x).
Proof.
  intros p q. specialize (H0 x). destruct H0. destruct equiv_isequiv0.
  unfold pointwise_paths in *. assert (id p = id q).
  - rewrite <- eisretr0. rewrite <- (eisretr0 q). unfold dot.



 
