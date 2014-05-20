module VecHS where

open import Vec
open import Data.Unit
open import Data.Nat.Show

open import IO
import IO.Primitive as P
  

main : P.IO ⊤
main = run f
  where f : IO ⊤
        f = putStrLn (show 5)
