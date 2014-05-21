module VecEpic where

open import Vec
--open import Data.Unit
--open import Data.Nat.Show

--open import IO
--import IO.Primitive as P

{-# BUILTIN NATURAL ℕ #-}

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
--  primCons   : a -> List a -> List a
{-# COMPILED_EPIC primNil (u : Unit) -> Any = primNil() #-}


--primitive primStringFromList :  List Char -> String
postulate
  primStringFromList   : (List Char) -> String

{-# COMPILED_EPIC primStringFromList (l : Any) -> String = primStringFromList(l) #-}

  
_>>_ : ∀ {A B} →  IO A → IO B → IO B
m₁ >> m₂ = m₁ >>= λ _ → m₂

main : IO ⊤
main = putStrLn (primStringFromList s) >> return tt
  where s : List Char
        s = primNil Char

show : ℕ -> List Char
show n = ?

