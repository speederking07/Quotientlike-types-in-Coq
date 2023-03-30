Require Import Bool.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Lib.EqDec.

Definition FunExt := forall (A B: Type) (f g: A -> B), (forall x: A, f x = g x) -> f = g.

Definition set (A: Type) : Type := A -> bool.


Definition set_filter {A: Type} (p: A-> bool) (s: set A) : set A :=
  fun x: A => if p x then s x else false.

Definition set_union {A: Type} (s s': set A) : set A :=
  fun x: A => (s x) || (s' x).

Definition set_intersection {A: Type} (s s': set A) : set A :=
  fun x: A => (s x) && (s' x).

Definition set_complement {A: Type} (s: set A) : set A :=
  fun x: A => negb (s x).

Definition set_add {A: Type} `{EqDec A} (a: A) (s: set A)  : set A :=
  fun x: A => if eqf x a then true else s x.

Fixpoint list_to_set {A: Type} `{EqDec A} (l: list A) : set A :=
match l with
| []        => fun _ => false
| (h :: l') => set_add h (list_to_set l')
end.

Theorem double_set_complement {A: Type} `{FunExt} `{EqDec A} (s: set A) :
  s = set_complement (set_complement s).
Proof.
  unfold set_complement. apply H. intros x. destruct (s x); auto.
Qed.

Theorem list_to_set_correct {A: Type} `{EqDec A} (l: list A) :
  forall x: A, reflect (In x l) (list_to_set l x).
Proof.
  intros x. destruct (list_to_set l x) eqn:e; constructor.
  - induction l; cbn in *; [inversion e|].
    unfold set_add in *. rewrite eqf_sym in e. destruct (eqf a x) eqn:e'.
    + left. apply eqf_iff. auto.
    + right. auto.
  - intros I. induction l; cbn in *; [inversion I|].
    unfold set_add in *. destruct I.
    + subst. rewrite eqf_refl in e. inversion e.
    + apply IHl; [|auto]. destruct (eqf x a); [inversion e | auto].
Qed.



Definition mset (A: Type) : Type := A -> nat.


Definition mset_filter {A: Type} (p: A-> bool) (s: mset A) : mset A :=
  fun x: A => if p x then s x else 0.

Definition mset_union {A: Type} (s s': mset A) : mset A :=
  fun x: A => (s x) + (s' x).

Definition mset_intersection {A: Type} (s s': mset A) : mset A :=
  fun x: A => min (s x) (s' x). 

Definition mset_add {A: Type} `{EqDec A} (a: A) (s: mset A)  : mset A :=
  fun x: A => if eqf x a then S (s x) else s x.

Fixpoint list_to_mset {A: Type} `{EqDec A} (l: list A) : mset A :=
match l with
| []        => fun _ => O
| (h :: l') => mset_add h (list_to_mset l')
end.