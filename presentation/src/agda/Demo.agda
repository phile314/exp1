module Demo where


data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat


data Vec {A : Set} : Nat -> Set where
  nil  : Vec zero
  cons : ∀ {n} -> A -> Vec {A} n -> Vec {A} (suc n)


head : ∀ {n A} -> Vec {A} (suc n) -> A
head (cons x v) = x
