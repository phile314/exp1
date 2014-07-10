module RSimpleUhc where


---------------------
------ Prelude ------
---------------------

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat
{-# COMPILED_CORE_DATA Nat RSimpleUhc.Nat (Zero,0) (Suc,1) #-}
{-# BUILTIN NATURAL Nat #-}

_plus_ : Nat → Nat → Nat
zero  plus n = n
suc m plus n = suc (m plus n)

_times_ : Nat → Nat → Nat
zero  times n = zero
suc m times n = n plus (m times n)

data Vec (a : Set) : Nat -> Set where
  Nil : Vec a zero
  Cons : {n : Nat} -> (x : a) -> (xs : Vec a n) -> Vec a (suc n)



head : {a : Set} {n : Nat}-> Vec a (suc n) -> a
head (Cons x xs) = x


----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : Nat} {a : Set} -> a -> Vec a n
pure {zero} x = Nil
pure {suc n} x = Cons x (pure x)


_apply_ : {a b : Set} {n : Nat} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil apply xs = Nil
Cons x fs apply Cons x₁ xs = Cons (x x₁) (fs apply xs)

vmap : {a b : Set} {n : Nat} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

vsum : ∀ {n} -> Vec Nat n -> Nat
vsum Nil = zero
vsum (Cons x v) = x plus vsum v

compute : Nat
compute = vsum (vmap (_plus_ 34) (pure {12} 23))

---------------------
------ MAIN    ------
---------------------


postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

postulate
  Char : Set


--private
postulate
  primNatToStr    : Nat → String


data Unit : Set where
  tt : Unit

postulate
    IO      : Set -> Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO Unit

{-# COMPILED_CORE return (\x -> UHC.Base.return x) #-}
{-# COMPILED_CORE _>>=_ (\x y -> $UHC.Base.$>$>$= x y) #-}
{-# COMPILED_CORE putStrLn (\x -> UHC.Base.putStrLn x) #-}

{- data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A -}


  
_>>_ : ∀ {A B} →  IO A → IO B → IO B
m1 >> m2 = m1 >>= λ _ → m2

main : IO Unit
main = putStrLn (primNatToStr compute) >> return tt



