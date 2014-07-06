module RSimpleEpic where


---------------------
------ Prelude ------
---------------------

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

data Vec (a : Set) : ℕ -> Set where
  Nil : Vec a zero
  Cons : {n : ℕ} -> (x : a) -> (xs : Vec a n) -> Vec a (suc n)



head : {a : Set} {n : ℕ}-> Vec a (suc n) -> a
head (Cons x xs) = x


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

vsum : ∀ {n} -> Vec ℕ n -> ℕ
vsum Nil = zero
vsum (Cons x v) = x + vsum v

compute : ℕ
compute = vsum (vmap (_+_ 34) (pure {12} 23))

---------------------
------ MAIN    ------
---------------------


postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

private
 primitive
  primCharToNat    : Char → ℕ
--  primCharEquality : Char → Char → Bool


data ⊤ : Set where
  tt : ⊤

postulate
    IO      : Set -> Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO ⊤

{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}
{-# COMPILED_EPIC _>>=_ (u1 : Unit, u2 : Unit, x : Any, f : Any) -> Any = iobind(x,f) #-}
{-# COMPILED_EPIC putStrLn (a : String , u : Unit) -> Unit = putStrLn(a) #-}

{- data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A -}

postulate
  List : Set -> Set

--{-# BUILTIN LIST List #-}
--{-# COMPILED_TYPE List List #-}

postulate
  primNil    : (a : Set) → List a
  primCons   : (a : Set) → a → List a → List a
{-# COMPILED_EPIC primNil (u : Unit) -> Any = primNil() #-}
{-# COMPILED_EPIC primCons (u : Unit, x : Any, xs : Any) -> Any = primCons(x,xs) #-}

--primitive primStringFromList :  List Char -> String
postulate
  primStringFromList   : (List Char) -> String
  bigToStr             : ℕ -> String

{-# COMPILED_EPIC primStringFromList (l : Any) -> String = primStringFromList(l) #-}
{-# COMPILED_EPIC bigToStr (x : BigInt) -> String = bigToStr(x) #-}
  
_>>_ : ∀ {A B} →  IO A → IO B → IO B
m₁ >> m₂ = m₁ >>= λ _ → m₂

main : IO ⊤
main = putStrLn (bigToStr compute) >> return tt



