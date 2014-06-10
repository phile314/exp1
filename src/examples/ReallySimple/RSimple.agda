module RSimple where

data Nat : Set where
  Zero : Nat
  Suc : Nat -> Nat

add : Nat -> Nat -> Nat
add Zero y = y
add (Suc x) y = Suc (add x y)
