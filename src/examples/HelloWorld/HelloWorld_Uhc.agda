module HelloWorld_Uhc where


---------------------
------ Prelude ------
---------------------

data Unit : Set where
  tt : Unit
{-# COMPILED_CORE_DATA Unit HelloWorld_Uhc_Pre.Unit (TT,0) #-}


postulate
  String : Set

{-# BUILTIN STRING String #-}

postulate
    IO      : Set -> Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO Unit

{-# COMPILED_CORE return (\a x -> HelloWorld_Uhc_Pre.return x) #-}
{-# COMPILED_CORE _>>=_ (\a b x y -> $HelloWorld_Uhc_Pre.$>$>$= x y) #-}
{-# COMPILED_CORE putStrLn System.IO.putStrLn #-}

-- fix the unit problem
postulate
  HsUnit : Set
  fixMain : IO Unit -> IO HsUnit
{-# COMPILED_CORE fixMain HelloWorld_Uhc_Pre.fixMain #-}

_>>_ : ∀ {A B} →  IO A → IO B → IO B
m1 >> m2 = m1 >>= λ _ → m2

main : IO HsUnit
main = fixMain (putStrLn "tesdfdsfg" >> return tt)
