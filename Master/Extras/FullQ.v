Require Import Qplus.
Require Import Integer.

Inductive FullQ :=
| QPos  : Qplus -> FullQ
| QZero : FullQ
| QNeg  : Qplus -> FullQ.

Fixpoint Qplus_inv (q: Qplus) : Qplus :=
match q with
| N x => D (Qplus_inv x)
| One => One
| D x => N (Qplus_inv x)
end.

Definition Qinv (q: FullQ) : FullQ :=
match q with
| QPos x => QPos (Qplus_inv x)
| QZero  => QZero
| QNeg x => QNeg (Qplus_inv x)
end.

Inductive Positive :=
| POne : Positive
| PS   : Positive -> Positive.

Fixpoint to_nat (p: Positive) : nat :=
match p with
| POne  => 1
| PS p' => S (to_nat p')
end.

Fixpoint to_nat_red (p: Positive) : nat :=
match p with
| POne  => 0
| PS p' => S (to_nat_red p')
end.

Fixpoint from_nat (p: nat) : Positive :=
match p with
| 0    => POne
| 1    => POne
| S p' => PS (from_nat p')
end.

Fixpoint from_nat_red (p: nat) : Positive :=
match p with
| 0    => POne
| S p' => PS (from_nat_red p')
end.

Definition Q' : Type := Z * Positive.

Definition Q'neg (q: Q') : Q' :=
  let (n, d) := q in (neg n, d).

Definition Q'inv (q: Q') : Q' :=
match q with
| (Pos n, d) => (Pos (to_nat_red d), from_nat_red n)
| (Zero, d)  => (Zero, d)
| (Neg n, d) => (Neg (to_nat_red d), from_nat_red n)
end.

Definition Padd (x y: Positive) : Positive :=
  from_nat ((to_nat x) + (to_nat y)).

Definition Pmul (x y: Positive) : Positive :=
  from_nat ((to_nat x) * (to_nat y)).

Definition to_Z (x: Positive) : Z :=
  Pos (to_nat_red x).

Definition Q'add (x y: Q') : Q' :=
match x y with
| (xn, xd), (yn, yd) => (add (mul xn (to_Z yd)) (), Pmul xd yd)
end.





