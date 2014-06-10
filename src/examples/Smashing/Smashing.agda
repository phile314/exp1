module Smashing where

data Nat where
  zero : Nat

data Refl {A : Set} (x : A) : A -> Set where
  refl : Refl x x

test : Refl
test = ?
