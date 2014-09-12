module HelloNat_Uhc where


---------------------
------ Prelude ------
---------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Unit : Set where
  tt : Unit
{-# BUILTIN UNIT Unit #-}

postulate
  String : Set
{-# BUILTIN STRING String #-}

postulate
    IO      : Set -> Set
    Integer : Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO Unit

    dbgNatToInteger : Nat -> Integer
    dbgIntegerToString : Integer -> String

{-# COMPILED_CORE return (\a x -> UHC.Agda.Builtins.primReturn x) #-}
{-# COMPILED_CORE _>>=_ (\a b x y -> UHC.Agda.Builtins.primBind x y) #-}
{-# COMPILED_CORE putStrLn (UHC.Agda.Builtins.primPutStrLn) #-}
{-# COMPILED_CORE dbgNatToInteger (UHC.Agda.Builtins.primDebugNatToInteger) #-}
{-# COMPILED_CORE dbgIntegerToString (UHC.Agda.Builtins.primDebugIntegerToString) #-}

natToStr : Nat -> String
natToStr x = dbgIntegerToString (dbgNatToInteger x)

_>>_ : ∀ {A B} →  IO A → IO B → IO B
m1 >> m2 = m1 >>= λ _ → m2

_+_ : Nat -> Nat -> Nat
zero + y = y
suc x + y = suc (x + y)

main : IO Unit
main = putStrLn (natToStr (34 + 12)) >> return tt
-- main = putStrLn "tesdfdsfg" >> return tt
