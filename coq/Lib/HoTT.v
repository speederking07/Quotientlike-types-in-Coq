Require Import Setoid.

Require Import Master.Lib.EqDec.

 
Notation "p ^" := (eq_sym p) (at level 30). 
Notation "! P" := (P -> False) (at level 60).
Notation "f @ g" := (eq_trans f g) (at level 40). 
Notation "f |> g" := (fun x => g (f x)) (at level 20). 
Notation "f <| g" := (fun x => f (g x)) (at level 20).
Notation "f == g" := (forall x, f x = g x) (at level 15).

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
  isHProp P -> WeaklyConstant (f |> g).
Proof.
  intros A B P f g isHProp. unfold WeaklyConstant. intros x y. assert (f x = f y).
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
  eq_refl = (p^) @ p.
Proof.
  intros A x y []. cbn. reflexivity.
Qed.

Lemma loop_eq' : forall A: Type, forall x y: A, forall p: x = y, 
  eq_refl = p @ (p^).
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
  intros A H x y. destruct (eqf x y) eqn: e.
  - left. apply eqf_iff. auto.
  - right. intros f. subst. rewrite eqf_refl in e. inversion e.
Qed.
  

Definition isLeft {A B: Type} (x : A + B): bool :=
  match x with
  | inl _ => true
  | _ => false
  end.

Theorem pathdec_eqDec : forall A: Type, DecidableEq A -> EqDec A.
Proof.
  intros A H. unfold DecidableEq in H. exists (fun x y => isLeft (H x y)).
  intros x y. destruct (isLeft (H x y)) eqn:e; constructor.
  - destruct (H x y); cbn in *; [auto | inversion e].
  - intros E. subst. destruct (H y y); cbn in *; [inversion e | auto].
Qed.

Theorem dec_eq_hset : forall A: Type, EqDec A -> isHSet A.
Proof.
  intros A H. apply pathdec_hset. apply eqDec_pathdec. assumption.
Qed.


Global Instance bool_is_HSet : isHSet bool.
Proof.
  apply dec_eq_hset. econstructor. exact Bool.eqb_spec.
Defined.

Global Instance nat_is_HSet : isHSet nat.
Proof.
  apply dec_eq_hset. econstructor. exact PeanoNat.Nat.eqb_spec.
Defined.


Definition path_contr {A: Type} `{isContr A} (x y: A) : x = y :=
  (contr x) @ ((contr y)^).

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

Theorem contr_not_eq_hprop : exists A: Type, isHProp A /\ (!isContr A).
Proof.
  exists False. split.
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

Theorem hprop_not_eq_hset : exists A: Type, isHSet A /\ (! isHProp A).
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

Theorem isHProp_deg : forall A: Type, isHProp A -> isNType HPropLevel A.
Proof.
  unfold isNType. cbn.
  intros A H p q. apply hprop_def. assumption.
Qed.

Theorem isHSet_def : forall A: Type, isNType HSetLevel A -> isHSet A.
Proof.
  unfold isNType. cbn.
  intros A H x y p q. destruct (H x y p q). assumption. 
Qed.

Theorem isHSet_deg : forall A: Type, isHSet A -> isNType HSetLevel A.
Proof.
  unfold isNType. cbn.
  intros A H x y p q. apply hprop_def. apply hset_def.
Qed.


Theorem NType_incusion {A: Type} (n : universe_level) :
  isNType n A -> isNType (S_universe n) A.
Proof.
  revert A.
  induction n; intros A H.
  - cbn in *; intros x y.
    apply contr_bottom.
    assumption.
  - simpl in *; intros x y.
    apply IHn.
    apply H.
Qed.




Definition ap {A B: Type} {x y: A} (f: A -> B) (p: x = y): f x = f y :=
  match p with
  | eq_refl => eq_refl
  end.

Definition transport {A: Type} {x y: A} {P: A -> Type} (path: x = y) (q : P x) : P y :=
match path with
| eq_refl => q
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

Theorem ap_comp {A B C: Type} {x y: A} (f: A -> B) (g: B -> C) (p: x = y)
  : ap g (ap f p) = ap (fun x => g (f x)) p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

Theorem ap_id {A B: Type} {x y: A} (p: x = y) : ap id p = p.
Proof.
  destruct p. cbn. reflexivity.
Qed.

(* transport proofs *)


Theorem transport_ap {A B: Type} {P: B -> Type} {x y: A} (f: A -> B) (p: x = y) (u: P (f x))
  : transport (P := P <| f) p u = transport (ap f p) u.
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

Class IsEquiv {A B : Type} (izo : A -> B) := {
  inv : B -> A ;
  eisretr : (izo <| inv) == id;
  eissect : (inv <| izo) == id;
  eisadj : (eisretr <| izo) == (ap izo <| eissect);
}.

Lemma eq_loop_mid {A: Type} (f: A -> A) (H : forall x, f x = x) (x y: A) (q : x = y) :  
  (H x ^) @ (ap f q) @ (H y) = q.
Proof.
  destruct q. cbn. symmetry. apply loop_eq.
Qed.

Lemma eq_loop_mid' {A: Type} {f: A -> A} (H: forall a, f a = a) {x y: A} (p: x = y) 
  : ap f p = (H x) @ p @ (H y ^).
Proof.
  destruct p. cbn. apply loop_eq'.
Qed.

Definition ap_swap_r {A : Type} {f : A -> A} (p : forall x, x = f x) 
  {x y : A} (q : x = y): p x @ ap f q = q @ p y.
Proof.
  destruct q. cbn. rewrite eq_trans_refl_l. reflexivity.
Qed.

Definition ap_swap_l {A : Type} {f : A -> A} (p : forall x, f x = x) 
  {x y : A} (q : x = y): ap f q @ p y = p x @ q.
Proof.
  destruct q. cbn. rewrite eq_trans_refl_l. reflexivity.
Qed.

Definition move_r (A : Type) (x y : A) (p q : x = y) : eq_refl = (p^) @ q -> p = q.
Proof.
  intros H. destruct p. cbn in *. rewrite H, eq_trans_refl_l. auto.
Qed.

Definition move_l (A : Type) (x y z : A) (p : x = z) (q : y = z) (r : x = y)
  : r @ q = p -> q = (r^) @ p.
Proof.
  intro H. destruct p, q. cbn in *. rewrite H. auto.
Qed.

Global Instance IsEquivTrans {A B C: Type} {f: A -> B} {g: B -> C}
  (Ef: IsEquiv f) (Eg: IsEquiv g) : IsEquiv (f |> g).
Proof.
  destruct Ef as (f', fr, fs, fa). destruct Eg as (g', gr, gs, ga).
  unshelve esplit; unfold id in *.
  - exact (f' <| g').
  - exact (fun c => (ap g (fr (g' c))) @ (gr c)).
  - exact (fun a => (ap f' (gs (f a))) @ (fs a)).
  - intros a. cbn.
    now rewrite <- (ap_comp f g), ap_distr, (ap_comp f' f), 
      <- (fa a), (ap_swap_l fr), ap_distr, <- ga.
Defined.

Definition makeIsEquiv {A B : Type} (f : A -> B) (g: B -> A)
  (retr : forall b : B, f (g b) = b) (sect : forall a : A, g (f a) = a) : IsEquiv f.
Proof.
  unshelve esplit.
  - exact g.
  - exact retr.
  - exact (fun x => ap g (ap f (sect x)^) @ ap g (retr (f x)) @ sect x).
  - intros x; unfold id in *.
    apply move_r.
    rewrite ap_distr, ap_distr, eq_trans_assoc, eq_trans_assoc,
      (ap_comp g f), (ap_swap_r (fun b => (retr b)^)),
      <- eq_trans_assoc, <- eq_trans_assoc. 
    apply move_l. 
    rewrite eq_trans_assoc, (ap_comp g f), 
      (ap_swap_r (fun b => (retr b)^)).
    now destruct (retr (f x)), (sect x).
Defined.

Arguments IsEquiv {A B}.

Class Equiv (A B: Type) := {
  izo: A -> B;
  equiv: IsEquiv izo;
}.

Class HEquiv (A B: Type) := {
  izo': A -> B;
  inv' : B -> A ;
  eisretr' : forall b : B, izo' (inv' b) = b;
  eissect' : forall a : A, inv' (izo' a) = a;
  eisadj' : forall a: A, eisretr' (izo' a) = ap izo' (eissect' a);
}.

Global Instance toHEquiv (A B: Type) `{Equiv A B} : HEquiv A B.
Proof.
  destruct H as (izo, (inv, eisretr, eissect, eisadj)).
  econstructor. apply eisadj.
Defined.

Global Instance toEquiv (A B: Type) `{HEquiv A B} : Equiv A B.
Proof.
  destruct H as (izo, inv, eisretr, eissect, eisadj).
  econstructor. econstructor. apply eisadj.
Defined.



Definition ap_rev {A B: Type} {f: A -> B} {g: B -> A} 
  (H: forall x: A, g (f x) = x) {x y: A} (p: f x = f y) : x = y
  := ((H x)^) @ (ap g p) @ (H y).

Lemma ap_rev_ap_id {A B: Type} {f: A -> B} {g: B -> A} (H: forall a, g (f a) = a) {x y: A} 
  : forall p : x = y, ap_rev H (ap f p) = p.
Proof.
  intros []. cbn. symmetry. apply loop_eq.
Qed.

Lemma ap_ap_rev_id {A B: Type} {f: A -> B} {g: B -> A} 
  {H: forall a, g (f a) = a} {H': forall b, f (g b) = b} 
  (adj : forall x, H' (f x) = ap f (H x)) {x y: A} 
  : forall p: f x = f y, (ap f (ap_rev H p)) = p.
Proof. 
  intros p. unfold ap_rev.
  rewrite ap_distr, ap_distr, (ap_comp g f), ap_inv.
  assert (E: forall h, ((H' (f x)) ^) @ (ap (fun x => f (g x)) h) @ H' (f y) = h)
    by apply (eq_loop_mid (fun x => f (g x))).
  now rewrite <- E, adj, adj.
Qed.

Lemma fun_id_apply_is_ap {A : Type} (f: A -> A) (H : forall a, f a = a)
  (a : A) : H (f a) = ap f (H a).
Proof.
Abort.

Lemma adj_sym {A B : Type} {f: A -> B} {g: B -> A}
  {H: forall a, g (f a) = a} {H': forall b, f (g b) = b}
  (adj: forall a, H' (f a) = ap f (H a))
  : forall b: B, H (g b) = ap g (H' b).
Proof.
  intros b. apply (ap_rev (f := ap f) (g := ap_rev H)).
  - intros p. apply ap_rev_ap_id.
  - rewrite <- adj, ap_comp. apply move_r.
    rewrite (ap_swap_r (fun x => H' (x) ^)).
    apply loop_eq'.
Defined.

Theorem equiv_path (A B: Type) (f: A -> B) :
  IsEquiv f -> forall x y: A, Equiv (x = y) (f x = f y).
Proof. 
  intros (g, retr, sect, adj) x y. econstructor.
  exact ( makeIsEquiv (ap f) (ap_rev sect) 
    (ap_ap_rev_id adj) (ap_rev_ap_id sect) ).
Defined.

Theorem equiv_keep_level (A B: Type) (n: universe_level) :
   isNType n A -> Equiv B A -> isNType n B.
Proof.
  revert A B. induction n; intros A B.
  - cbn. intros (a, loop) (f, (g, _, retr, _)). unfold id in *.
    econstructor. intros b. now rewrite <- (retr b), (loop (f b)).
  - cbn. intros H (f, (g, sect, retr, adj)) x y. 
    apply (IHn (f x = f y)); [auto | ].
    apply equiv_path. 
    econstructor; apply adj.
Defined.


(* Equiv is equivalance relation *)

Global Instance Equiv_refl {A: Type} : (Equiv A A).
Proof.
  exists id. unshelve econstructor.
  - exact id.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Global Instance Equiv_sym {A B: Type} `{Equiv A B} : (Equiv B A).
Proof.
  destruct H as (izo, (inv, eisretr, eissect, eisadj)).
  exists inv. econstructor. apply (adj_sym eisadj).
Defined.

Global Instance Equiv_trans {A B C: Type} (E : Equiv A B) (E' : Equiv B C) : (Equiv A C).
Proof.
  destruct E as (f, Ef). destruct E' as (g, Eg).
  exists (f |> g). apply IsEquivTrans; auto.
Defined.


(* Function paths *)

Definition happly {A: Type} {B: A-> Type}  {f g : forall x: A, B x} 
  (p : f = g) (x : A) : f x = g x :=
match p with
| eq_refl => eq_refl
end.

Definition HFunExt : Type := forall (A: Type) (B: A -> Type) (f g: forall a: A, B a), 
  IsEquiv (happly (f := f) (g := g)).

Lemma fun_is_img_hprop (A: Type) (B: A -> Type) (funExt : HFunExt) :
  (forall a: A, isHProp (B a)) -> isHProp (forall a: A, B a).
Proof.
  unfold isHProp. intros H f g. destruct (funExt A B f g) as (inv, _, _, _). 
  apply inv. intros x. apply H.
Qed.


Lemma fun_is_img_contr (A: Type) (B: A -> Type) (funExt: HFunExt) :
   (forall a: A, isContr (B a)) -> isContr (forall a: A, B a).
Proof.
  assert (C': forall T: Type, T * (isHProp T) -> isContr T).
  { intros T (c, hprop). exists c. intros t. apply hprop. }
  intros H. apply C'. split.
  - intros a. destruct (H a). assumption.
  - apply fun_is_img_hprop; [auto |]. intros a b b'. destruct (H a) as (c, l).
    rewrite (l b), (l b'). auto. 
Qed. 

Lemma fun_is_img_level_dep (A: Type) (B: A -> Type) (n: universe_level) (funExt: HFunExt) :
   (forall a: A, isNType n (B a)) -> isNType n (forall a: A, B a).
Proof.
  revert A B. induction n; intros A B H; cbn in *.
  - apply fun_is_img_contr; auto.
  - intros f g. apply (equiv_keep_level (forall x : A, f x = g x)).
    + apply IHn. intros a. apply H.
    + destruct (funExt A B f g) as (inv, rets, sect, adj).
      econstructor; econstructor; apply adj.
Qed.

Lemma fun_is_img_level (A B: Type) (n: universe_level) (funExt: HFunExt) :
   isNType n B -> isNType n (A -> B).
Proof.
  intros H. apply (fun_is_img_level_dep A (fun _ => B)); auto.
Qed.
