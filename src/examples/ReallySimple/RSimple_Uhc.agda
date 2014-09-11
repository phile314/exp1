module RSimple_Uhc where


---------------------
------ Prelude ------
---------------------

data Unit : Set where
  tt : Unit
{-# COMPILED_CORE_DATA Unit RSimple_Uhc_Pre.Unit (TT,0) #-}

data Nat : Set where
  zero : Nat
  suc  : (n : Nat) → Nat
{-# COMPILED_CORE_DATA Nat RSimple_Uhc_Pre.Nat (Zero,0) (Suc,1) #-}
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


postulate
  primNatToStr    : Nat → String
{-# COMPILED_CORE primNatToStr (\x -> RSimple_Uhc_Pre.primNatToStr x) #-}

postulate
    IO      : Set -> Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO Unit

{-# COMPILED_CORE return (\a x -> RSimple_Uhc_Pre.return x) #-}
{-# COMPILED_CORE _>>=_ (\a b x y -> $RSimple_Uhc_Pre.$>$>$= x y) #-}
{-# COMPILED_CORE putStrLn System.IO.putStrLn #-}

-- fix the unit problem
postulate
  HsUnit : Set
  fixMain : IO Unit -> IO HsUnit
{-# COMPILED_CORE fixMain RSimple_Uhc_Pre.fixMain #-}

 
_>>_ : ∀ {A B} →  IO A → IO B → IO B
m1 >> m2 = m1 >>= λ _ → m2

main : IO HsUnit
main = fixMain (putStrLn (primNatToStr 234) >> return tt)
-- main = fixMain (primNatToStr compute) >> return tt)




