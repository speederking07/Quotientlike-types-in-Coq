Require Import Setoid.
Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Master.Lib.Sorted.
Require Import Master.Lib.EqDec.
Require Import Master.Lib.LinearOrder.

Definition PredPerm {A : Type} `{EqDec A} (l l' : list A) :=
  forall p : A -> bool, count p l = count p l'.

Definition ElemPerm {A : Type} `{EqDec A} (l l' : list A) :=
  forall x: A, count (eqf x) l = count (eqf x) l'.

Inductive DefPerm {A : Type} : list A -> list A -> Prop :=
| perm_nil: DefPerm [] []
| perm_skip x l l' : DefPerm l l' -> DefPerm (x::l) (x::l')
| perm_swap x y l : DefPerm (y::x::l) (x::y::l)
| perm_trans l l' l'' : DefPerm l l' -> DefPerm l' l'' -> DefPerm l l''.



Lemma PredPerm_is_perm {A: Type} `{LinearOrder A} (l l': list A) : PredPerm l l' <-> permutation l l'.
Proof.
  unfold PredPerm, permutation. split; intros P p; apply P; auto.
Qed.

Fixpoint remove {A: Type} `{EqDec A} (x: A) (l: list A) :=
match l with 
| []     => []
| (h::t) => if eqf x h then t else h :: remove x t
end.

Lemma remove_count_true {A: Type} `{EqDec A} (h: A) (l: list A) (p: A -> bool) :
  In h l -> p h = true -> count p l = S (count p (remove h l)).
Proof.
  induction l; intros I t.
  - cbn in *. destruct I. 
  - cbn in *. destruct I.
    + subst. rewrite t. rewrite eqf_refl. auto.
    + destruct (p a) eqn:e; destruct (eqf h a) eqn:e1; auto.
      * cbn in *. rewrite e. rewrite IHl; auto.
      * rewrite <- eqf_iff in e1. subst. rewrite t in e. discriminate.
      * cbn in *. rewrite e. apply IHl; auto.
Qed.

Lemma remove_count_false {A: Type} `{EqDec A} (h: A) (l: list A) (p: A -> bool) :
  p h = false -> count p l = count p (remove h l).
Proof.
  induction l; intros f; auto. cbn in *. 
  destruct (p a) eqn:e; destruct (eqf h a) eqn:e1; auto.
  - rewrite <- eqf_iff in e1. subst. rewrite f in e. discriminate.
  - cbn. rewrite e. f_equal. apply IHl; auto.
  - cbn. rewrite e. apply IHl; auto.
Qed.

Lemma in_count_not_O {A: Type} `{EqDec A} (l: list A) (x: A) :
  In x l <-> count (eqf x) l <> O.
Proof.
  split.
  - intros I. induction l.
    + cbn in I. destruct I.
    + cbn in *. destruct I as [e|I].
      * subst. rewrite eqf_refl. auto.
      * destruct (eqf x a) eqn: e; auto.
  - intros C. induction l.
    + cbn in C. contradiction.
    + cbn in *. destruct (eqf x a) eqn: e; auto. rewrite <- eqf_iff in e.
      subst. left. auto.
Qed. 

Lemma perm_in {A: Type} `{EqDec A} (l l': list A) (x: A) :
  PredPerm l l' -> In x l -> In x l'.
Proof.
  intros perm I. rewrite in_count_not_O. rewrite in_count_not_O in I.
  specialize (perm (eqf x)). rewrite <-perm. assumption.
Qed.

Lemma remove_perm {A: Type} `{EqDec A} (h: A) (l l': list A) :
  PredPerm (h :: l) l' -> PredPerm l (remove h l').
Proof.
  unfold PredPerm. revert l'. induction l; intros l' perm p.
  - assert (In h l'). 
    + apply (perm_in [h]); auto. cbn. auto. 
    + cbn. apply eq_add_S. specialize (perm p). cbn in *. destruct (p h) eqn:e.
      * rewrite <-remove_count_true; auto.
      * rewrite <-remove_count_false; auto.
  - assert (In h l') by (apply (perm_in (h::a::l)); cbn; auto).
    assert (In a l') by (apply (perm_in (h::a::l)); cbn; auto).
    cbn. apply eq_add_S. apply eq_add_S. specialize (perm p). cbn in *.
    destruct (p h) eqn:e.
    + rewrite <-remove_count_true; auto.
    + rewrite <-remove_count_false; auto.
Qed.

Lemma remove_perm' {A: Type} `{EqDec A} (h: A) (l l': list A) :
  In h l' -> PredPerm l (remove h l') -> PredPerm (h :: l) l' .
Proof.
  unfold PredPerm. revert l'. induction l; intros l' I perm p.
  - cbn in *. specialize (perm p). destruct (p h) eqn: e.
    + rewrite (remove_count_true h); auto.
    + rewrite (remove_count_false h); auto.
  - cbn in *. specialize (perm p). destruct (p h) eqn: e.
    + rewrite (remove_count_true h l'); auto.
    + rewrite (remove_count_false h l'); auto.
Qed.

(* PredPerm and ElemPerm equivalance *)
Theorem pred_elem_prem_equiv {A: Type} `{EqDec A} (l l': list A) : 
  PredPerm l l' <-> ElemPerm l l'.
Proof.
  split.
  - intros P x. apply P.
  - revert l'. induction l; intros l' E p.
    + destruct l'; auto. specialize (E a). cbn in E. rewrite eqf_refl in E. inversion E.
    + rewrite (remove_perm' a l l'); auto.
      * rewrite in_count_not_O. specialize (E a). rewrite <- E. cbn. rewrite eqf_refl. auto.
      * intros p'. apply IHl. intros x. specialize (E x). cbn in *. destruct (eqf x a) eqn:e.
        -- apply eq_add_S. rewrite E. rewrite (remove_count_true a); auto.
           rewrite <- eqf_iff in e. subst. rewrite in_count_not_O. rewrite <- E. auto.
        -- rewrite E. rewrite (remove_count_false a); auto.
Qed.




Lemma elem_perm_nil {A: Type} {D: EqDec A} (l : list A) : ElemPerm [] l -> l = [].
Proof.
  intros H. destruct l; auto. specialize (H a). cbn in *. 
  rewrite eqf_refl in H. discriminate H.
Qed.

Lemma def_perm_relf {A: Type} (l : list A) : DefPerm l l.
Proof.
  induction l; constructor. assumption.
Qed.

Lemma remove_cons_def_perm {A: Type} {D: EqDec A} (h: A) (l: list A) :
  In h l -> DefPerm (h :: remove h l) l.
Proof.
  intros I. induction l; cbn in *; destruct I.
  - subst. rewrite eqf_refl. constructor. apply def_perm_relf.
  - destruct (eqf h a) eqn:e.
    + rewrite <- eqf_iff in e. subst. constructor. apply def_perm_relf.
    + apply (perm_trans (h :: a :: remove h l) (a :: h :: remove h l) (a :: l));
      constructor. apply IHl. assumption.
Qed.

Lemma remove_defperm' {A: Type} {D: EqDec A} (h: A) (l l': list A) :
  In h l' -> DefPerm l (remove h l') -> DefPerm (h :: l) l' .
Proof.
  intros I H. destruct l'.
  - cbn in I. destruct I.
  - cbn in *. destruct (eqf h a) eqn:e.
    + rewrite <- eqf_iff in e. subst. constructor. assumption.
    + apply (perm_trans (h :: l) (a :: h :: remove h l') (a :: l')).
      * apply (perm_trans (h :: l) (h :: a :: remove h l') (a :: h :: remove h l'));
        constructor. assumption.
      * constructor. apply remove_cons_def_perm; destruct I; auto. subst.
        rewrite eqf_refl in e. discriminate.
Qed.

(* DefPerm and ElemPerm equivalance for types with deciadable equality *)
Theorem def_elem_prem_equiv {A: Type} {D: EqDec A} (l l': list A) : 
  DefPerm l l' <-> ElemPerm l l'.
Proof.
  unfold ElemPerm. split.
  - intros H x. induction H; auto.
    + cbn. rewrite IHDefPerm. auto.
    + cbn. destruct (eqf x y), (eqf x x0); auto.
    + rewrite IHDefPerm1. assumption.
  - revert l'. induction l; intros l' H.
    + assert (l' = []) by (apply elem_perm_nil; assumption). subst. constructor.
    + specialize (IHl (remove a l')). assert (DefPerm l (remove a l')).
      * apply IHl. intro x. apply remove_perm. apply pred_elem_prem_equiv. assumption.
      * apply remove_defperm'; auto. specialize (H a). cbn in *. rewrite eqf_refl in H.
        rewrite in_count_not_O, <- H. auto.
Qed.

