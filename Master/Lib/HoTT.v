Require Import Setoid.

Inductive Empty : Type := .


Definition dot {A B C} (f: B -> C) (g: A -> B) := fun (x: A) => f (g x).

Notation "f $ g" := (dot f g) (at level 75). 
Notation "! f" := (f -> Empty) (at level 75). 
Notation "p ^" := (eq_sym p) (at level 30). 
Notation "f @ g" := (eq_trans f g) (at level 40). 

Class Decidable (A : Type) :=
  dec : A + (A -> False).

Class DecidableEq (A : Type) :=
  dec_eq : forall x y: A, Decidable (x = y).
Arguments dec A {_}.

Class isContr (A: Type) := ContrBuilder {
  center : A;
  contr : forall x: A, x = center
}.

Class isHProp (P : Type) :=
  hProp : forall p q : P, p = q.

Class isHSet (X : Type) := 
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
  collapse        : A -> A ;
  wconst_collapse : forall x y: A, collapse x = collapse y
}.

Theorem map_tought_isHProp : forall A B P: Type, forall f: A -> P, forall g: P -> B,
  isHProp P -> WeaklyConstant (g $ f).
Proof.
  intros A B P f g isHProp. unfold WeaklyConstant. intros x y. unfold dot. assert (f x = f y).
  - destruct (isHProp  (f x) (f y)). reflexivity.
  - destruct H. reflexivity.
Qed.

Theorem dec_is_collaps : forall A : Type, Decidable A -> Collapsible A.
Proof.
  intros A eq. destruct eq.
  - exists (fun x => a). intros x y. reflexivity.
  - exists (fun x => x); intros x y.
    exfalso; apply f; assumption.
Qed.

Class PathCollapsible (A : Type) :=
  path_coll : forall (x y : A), Collapsible (x = y).

Theorem eq_dec_is_path_collaps : forall A : Type, DecidableEq A -> PathCollapsible A.
Proof.
  intros A dec x y. apply dec_is_collaps. apply dec.
Qed.

Lemma loop_eq : forall A: Type, forall x y: A, forall p: x = y, 
  eq_refl = eq_trans (eq_sym p) p.
Proof.
  intros A x y []. cbn. reflexivity.
Qed.

Lemma loop_eq' : forall A: Type, forall x y: A, forall p: x = y, 
  eq_refl = p @ (p ^).
Proof.
  intros A x y []. cbn. reflexivity.
Qed.

Theorem path_collaps_is_hset (A : Type) : PathCollapsible A -> isHSet A.
Proof.
  unfold isHSet, PathCollapsible; intros C x y.
  cut (forall e: x=y, e = eq_trans (eq_sym(collapse(eq_refl x))) (collapse e)).
  - intros H p q. 
    rewrite (H q), (H p), (wconst_collapse p q).
    reflexivity.
  - intros []. apply loop_eq.
Qed.

Theorem pathdec_hset (A: Type) : DecidableEq A -> isHSet A.
Proof.
  intros H. apply path_collaps_is_hset. apply eq_dec_is_path_collaps. assumption.
Qed.

Theorem eqDec_pathdec : forall A: Type, EqDec A -> DecidableEq A.
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

Theorem pathdec_eqDec : forall A: Type, DecidableEq A -> EqDec A.
Proof.
  intros A H. unfold DecidableEq in H. exists (fun x y => isLeft (H x y)).
  intros x y. split.
  - case_eq (H x y); intros p H1.
    + intros _. assumption.
    + cbn. intro H2. discriminate.
  - intro H1. subst. case_eq (H y y); intros p H1.
    + cbn. reflexivity.
    + contradiction.
Qed.

Theorem dec_eq_hset : forall A: Type, EqDec A -> isHSet A.
Proof.
  intros A H. apply pathdec_hset. apply eqDec_pathdec. assumption.
Qed.

Definition path_contr {A: Type} `{isContr A} (x y: A) : x = y :=
 eq_trans (contr x) (eq_sym (contr y)).

Lemma all_path_eq_in_contr {A: Type} `{isContr A} {x y: A}: forall p q: x = y, p = q.
Proof.
  intros p q. assert (forall e: x = y, e = path_contr x y).
  - intros []. unfold path_contr. unfold contr. destruct H. apply loop_eq'.
  - rewrite (H0 p). rewrite (H0 q). reflexivity.
Qed.

Lemma contr_bottom (A: Type) `{isContr A} (x y: A): isContr (x = y).
Proof.
  exists (path_contr x y).
  intros p. apply all_path_eq_in_contr.
Qed.

Theorem contr_is_hprop (A: Type) `{isContr A} : isHProp A.
Proof.
  unfold isHProp. intros p q. destruct H. rewrite contr0.
  specialize (contr0 p). rewrite contr0. reflexivity.
Qed.

Theorem contr_not_eq_hprop : exists A: Type, isHProp A /\ (! isContr A).
Proof.
  exists Empty. split.
  - unfold isHProp. intros [] _.
  - intros []. destruct center0.
Qed. 

Lemma all_path_eq_in_hprop {A: Type} `{isHProp A} {x y: A}: forall p q: x = y, p = q.
Proof.
  intros p q. assert (isHProp (x=y)).
  - apply contr_is_hprop. apply contr_bottom. exists x. intro z. apply H.
  - apply H0. 
Qed.

Theorem hprop_def (A: Type) `{isHProp A} (x y: A) : isContr (x = y).
Proof.
  exists (H x y). intro p. apply all_path_eq_in_hprop.
Qed.

Theorem hprop_inv (A: Type) `{isContr A} (x y: A) : isHProp (x = y).
Proof.
  apply contr_is_hprop. apply contr_bottom. assumption.
Qed.

Theorem hprop_is_hset (A: Type) `{isHProp A} : isHSet A.
Proof.
  unfold isHSet. intros x y p q. apply all_path_eq_in_hprop.
Qed.

Theorem hprop_not_eq_hset : exists A: Type, isHSet A /\ !isHProp A.
Proof.
  exists bool. split.
  - apply pathdec_hset. intros x y. unfold Decidable. 
    destruct x, y; auto; right; intro H; discriminate.
  - intro H. specialize (H true false). discriminate.
Qed.

Theorem hset_def {A: Type} `{isHSet A} (x y: A) : isHProp (x = y).
Proof.
  unfold isHProp. apply H.
Qed. 

Theorem paths_between_paths_are_eq_in_hset {A: Type} `{isHSet A} {x y: A} {a b: x = y}:
 forall p q: a = b, p = q.
Proof.
  intros p q. assert (isContr (p = q)). 
  - unfold isHSet in H. apply contr_bottom. apply contr_bottom. exists a. intro c. apply H.
  - destruct H0. assumption.
Qed. 

Theorem hset_inv {A: Type} `{isHProp A} (x y: A) : isHSet (x = y).
Proof.
  intros a b p q. assert (isHSet A) by (apply hprop_is_hset; assumption).
  apply paths_between_paths_are_eq_in_hset.
Qed.





Inductive universe_level : Type :=
| minus_two  : universe_level
| S_universe : universe_level -> universe_level.

Definition HPropLevel := S_universe minus_two.

Definition HSetLevel := S_universe HPropLevel.

Fixpoint isNType (n : universe_level) (A : Type) : Type :=
match n with
| minus_two => isContr A
| S_universe n' => forall x y: A, isNType n' (x = y)
end.

Theorem isHProp_def : forall A: Type, isNType HPropLevel A -> isHProp A.
Proof.
  unfold isNType. cbn.
  intros A H p q. destruct (H p q). assumption. 
Qed.

Theorem isHProp_def' : forall A: Type, isHProp A -> isNType HPropLevel A.
Proof.
  unfold isNType. cbn.
  intros A H p q. apply hprop_def. assumption.
Qed.

Theorem isHSet_def : forall A: Type, isNType HSetLevel A -> isHSet A.
Proof.
  unfold isNType. cbn.
  intros A H x y p q. destruct (H x y p q). assumption. 
Qed.

Theorem isHSet_def' : forall A: Type, isHSet A -> isNType HSetLevel A.
Proof.
  unfold isNType. cbn.
  intros A H x y p q. apply hprop_def. apply hset_def.
Qed.


Theorem NType_incusion : forall A: Type, forall n : universe_level,
  isNType n A -> isNType (S_universe n) A.
Proof.
  intros A n; revert A.
  induction n; intros A H.
  - cbn in *; intros x y.
    apply contr_bottom.
    assumption.
  - simpl in *; intros x y.
    apply IHn.
    apply H.
Qed.





Definition id {A: Type} (x: A) := x.

Definition ap {A B: Type} {x y: A} (f: A -> B) (p: x = y): f x = f y :=
  match p with
  | eq_refl => eq_refl
  end.

Definition transport {A: Type} {x y: A} {P: A -> Type} (path: x = y) (q : P x) : P y :=
match path with
| eq_refl => q
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
  existT P x p = existT P y q -> exists path: x = y, transport path p = q.
Proof.
  intros A P x y p q H. inversion H.
  exists eq_refl. cbn. trivial.
Qed.

Theorem dep_pair_eq_inv : forall (A: Type) (P: A -> Type) (x y: A) (p: P x) (q: P y),
   (exists e: x = y, transport e p = q) -> existT P x p = existT P y q.
Proof.
  intros A P x y p q (-> & []). cbn. reflexivity.
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
  contr_equiv : forall y: B, isContr(exists x, f x = y).


Theorem equiv_same (A B: Type) (f: A -> B) `{IsEquiv A B f} : IsEquiv' f.
Proof.
  destruct H. exists equiv_inv0 equiv_inv0; assumption.
Qed.

Theorem equiv_same' (A B: Type) (f: A -> B) `{IsEquiv' A B f} : IsEquiv f.
Proof.
  assert (f $ (equiv_inv_A $ f $ equiv_inv_B) == id).
Abort.

Record qinv {A B: Type} (f: A -> B) := {
  g: B -> A;
  inv_l: g $ f == id;
  inv_r: f $ g == id;
}.

Theorem bad {A B: Type} (f: A -> B) : qinv f -> (qinv f = forall x: A, x = x).
Proof.
  intros [].
Abort.



 
