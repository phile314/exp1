module Vec where

open import Data.Nat


---------------------
------ Prelude ------
---------------------

data Vec (a : Set) : ℕ -> Set where
  Nil : Vec a 0
  Cons : {n : ℕ} -> (x : a) -> (xs : Vec a n) -> Vec a (suc n)



head : {a : Set} {n : ℕ}-> Vec a (suc n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : ℕ} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x


----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : ℕ} {a : Set} -> a -> Vec a n
pure {zero} x = Nil
pure {suc n} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : ℕ} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> xs = Nil
Cons x fs <*> Cons x₁ xs = Cons (x x₁) (fs <*> xs)

vmap : {a b : Set} {n : ℕ} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> ℕ -> ℕ -> Set
Matrix a n m = Vec (Vec a m) n

-- Define matrix addition
madd : {n m : ℕ} -> Matrix ℕ m n -> Matrix ℕ m n -> Matrix ℕ m n
madd a b = vmap (λ x → \y -> vmap _+_ x <*> y) a <*> b

-- Define the identity matrix
idMatrix : {n : ℕ} -> Matrix ℕ n n
idMatrix {zero} = Nil
idMatrix {suc n} = Cons (Cons 1 (pure n)) (vmap (λ x → Cons 0 x) idMatrix)

-- Define matrix transposition
tail : {n : ℕ} {a : Set} -> Vec a (suc n) -> Vec a n
tail (Cons x x₁) = x₁
transpose : {n m : ℕ} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {zero} {zero} a₁ = Nil
transpose {zero} {suc m} {a} x = Nil
transpose {suc n} {zero} a₁ = pure Nil
transpose {suc n} {suc m} {a} (Cons x₁ x₂) with vmap head (Cons x₁ x₂) 
... | vm = Cons vm (vmap (λ p → λ q → Cons p q) (tail x₁) <*> transpose (vmap tail x₂))
  
