module HelloWorld_Uhc where


---------------------
------ Prelude ------
---------------------

data Unit : Set where
  tt : Unit
{-# BUILTIN UNIT Unit #-}


postulate
  String : Set
{-# BUILTIN STRING String #-}

postulate
    IO      : Set -> Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO Unit

{-# COMPILED_CORE return (\a x -> UHC.Agda.Builtins.primReturn x) #-}
{-# COMPILED_CORE _>>=_ (\a b x y -> UHC.Agda.Builtins.primBind x y) #-}
{-# COMPILED_CORE putStrLn (UHC.Agda.Builtins.primPutStrLn) #-}

_>>_ : ∀ {A B} →  IO A → IO B → IO B
m1 >> m2 = m1 >>= λ _ → m2

main : IO Unit
main = putStrLn "Hello World" >> return tt
