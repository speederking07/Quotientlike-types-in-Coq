CoInductive delayed (A : Type) := Delayed {
  state : A + delayed A
}.

Arguments Delayed {A}.
Arguments state {A} _.

Definition delayed_val {A : Type} (x: A) := Delayed (inl x).
Definition delayed_del {A : Type} (x: delayed A) := Delayed (inr x).

CoFixpoint map {A B: Type} (f : A -> B) (x : delayed A) : delayed B :=
  match state x with
  | inl a => delayed_val (f a)
  | inr x' => delayed_del (map f x')
  end.

Definition pure {A: Type} (v: A) := delayed_val v.

CoFixpoint bind {A B: Type} (x : delayed A) (f : A -> delayed B) : delayed B :=
  match state x with
  | inl a => f a
  | inr x' => delayed_del (bind x' f)
  end.

CoFixpoint constDelayed {A: Type} (x: A) (t: nat) : delayed A :=
  match t with
  | O => delayed_val x
  | S t' => delayed_del (constDelayed x t')
  end.

Definition id {A: Type} (x: A) := x.

Lemma eq_delayed : forall {A : Type} (x y : delayed A), state x = state y -> x = y.
Proof.
  now intros A [] []; cbn; intros [].
Qed.

Inductive EqDelayed {A: Type} : delayed A -> delayed A -> Prop :=
| EqRes : forall x: A, EqDelayed (delayed_val x) (delayed_val x)
| EqDel : forall x y : delayed A, EqDelayed x y -> EqDelayed (delayed_del x) (delayed_del y).

CoInductive Eq_delayed {A: Type} : delayed A -> delayed A -> Prop :=
  state_eq : forall x y : delayed A,
    (exists v: A, state x = inl v /\ state y = inl v) \/
    (exists x' y': delayed A, Eq_delayed x' y' /\ state x = inr x' /\ state y = inr y')
     -> Eq_delayed x y.

Lemma map_id (A: Type) (x: delayed A) : Eq_delayed (map id x) x.
Proof.
  revert A x. cofix CH. destruct x as [[v | d]].
  - constructor. left. exists v. cbn. split; reflexivity.
  - constructor. right. cbn. exists (map id d), d. split; cycle 1. split; auto.
    apply CH.
Qed.

Definition dot {A B C: Type} (f : B -> C) (g: A -> B) (x: A) := f (g x).
Notation "f (.) g" := (dot f g) (at level 75). 

Lemma map_comp (A B C: Type) (f : B -> C) (g: A -> B) (x: delayed A) : 
  Eq_delayed (map (f (.) g) x) (map f (map g x)).
Proof.
  revert A B C f g x. cofix CH. destruct x as [[v | d]].
  - constructor. left. exists (f (g v)). unfold dot. cbn. split; auto.
  - constructor. right. cbn. exists (map (f (.) g) d), (map f (map g d)).
    split; cycle 1. split; auto. apply CH.
Qed.

Lemma left_id_bind (A B : Type) (f: A -> delayed B) (x: A) : 
  Eq_delayed (bind (pure x) f) (f x).
Proof.
  unfold pure, delayed_val. destruct (bind {| state := inl x |} f) eqn:e.
  constructor. destruct state0.
Abort.

Lemma right_id_bind (A B : Type) (x: delayed A) : 
  Eq_delayed (bind x pure) x.
Proof.
  revert A x. cofix CH. destruct x as [[v | d]].
  - constructor. left. exists v. cbn. split; reflexivity.
  - constructor. right. cbn. exists (bind d pure), d. split; cycle 1. split; auto.
    apply CH.
Qed.

Lemma bind_comp (A B C: Type) (f : B -> delayed C) (g: A -> delayed B) (x: delayed A) : 
  Eq_delayed (bind (bind x g) f) (bind x (fun y => bind (g y) f)).
Proof.
  revert A B C f g x. cofix CH. destruct x as [[v | d]].
  - constructor. left. exists (f (g v)). unfold dot. cbn. split; auto.
  - constructor. right. cbn. exists (map (f (.) g) d), (map f (map g d)).
    split; cycle 1. split; auto. apply CH.
Qed.

  

