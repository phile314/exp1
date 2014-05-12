module HelloWorld where

open import Data.Nat
open import Data.Nat.Show
open import Data.Unit
open import IO
import IO.Primitive as P

---------------------
------ Prelude ------
---------------------



main : P.IO ⊤
main = run f
  where f : IO ⊤
        f = putStrLn (show 5)
