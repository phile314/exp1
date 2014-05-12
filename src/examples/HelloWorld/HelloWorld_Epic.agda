module HelloWorld_Epic where

open import Data.Nat
open import Data.Nat.Show
open import Data.Unit
--open import IO.Epic.Strict
open import Data.String

postulate
    IO      : Set -> Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO ⊤

{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}
{-# COMPILED_EPIC _>>=_ (u1 : Unit, u2 : Unit, x : Any, f : Any) -> Any = iobind(x,f) #-}
{-# COMPILED_EPIC putStrLn       putStrLn              #-}





main : IO ⊤
main = f
  where f : IO ⊤
        f = putStrLn (show 5)
