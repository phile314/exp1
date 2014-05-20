module VecHS where

open import Vec
open import Data.Unit
open import Data.Nat renaming (ℕ to Nat)
open import Data.Nat.Show

open import IO
import IO.Primitive as P
  

toStdNat : ℕ -> Nat
toStdNat zero = zero
toStdNat (suc n) = suc (toStdNat n)


main : P.IO ⊤
main = run f
  where f : IO ⊤
        f = putStrLn (show (toStdNat compute))
