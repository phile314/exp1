module VecEpic where

open import Vec
--open import Data.Unit
--open import Data.Nat.Show

--open import IO
--import IO.Primitive as P

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}


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
  
_>>_ : ∀ {A B} →  IO A → IO B → IO B
m₁ >> m₂ = m₁ >>= λ _ → m₂

main : IO ⊤
main = putStrLn "34" >> return tt
--  where f : IO ⊤
--        f = putStrLn (show compute)
