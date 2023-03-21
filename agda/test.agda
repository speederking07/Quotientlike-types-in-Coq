{-# OPTIONS --cubical #-}

open import Agda.Builtin.Equality

data S¹ : Set where
  base : S¹
  loop : base ≡ base

data Torus : Set where
  point : Torus
  line1 : point ≡ point
  line2 : point ≡ point
  square : PathP (λ i → line1 i ≡ line1 i) line2 line2

data Nat : Set where
    zero : Nat
    suc : Nat -> Nat

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data Bag (X : Set) : Set where
  nil : Bag X
  cons : X -> Bag X -> Bag X
  swap : (x y : X) (z : Bag X) -> cons x (cons y z) ≡ cons y (cons x z)

_+_ : Nat -> Nat -> Nat
zero + y = y
(suc x) + y = suc (x + y)

half : Nat -> Nat
half zero              = zero
half (suc zero)     = zero
half (suc (suc n)) = suc (half n)


