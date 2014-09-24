module TypeErasureAgda where

data List {a} (A : Set a) : Set a where
  nil : List A
  cons : (x : A) -> (xs : List A) -> List A

map : forall {a b} -> {A : Set a} -> {B : Set b} -> (A -> B) -> List A -> List B
map f nil = nil
map f (cons x xs) = cons (f x) (map f xs)

data Unit : Set where
  unit : Unit

test : List Unit
test = map (\x -> x) (cons unit nil)

data Dummy : Set where


