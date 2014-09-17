module HelloDat_Uhc where


---------------------
------ Prelude ------
---------------------

data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data Bool : Set where
  true : Bool
  false : Bool
{-# BUILTIN BOOL Bool #-}
{-# BUILTIN TRUE true #-}
{-# BUILTIN FALSE false #-}

data Unit : Set where
  tt : Unit
{-# BUILTIN UNIT Unit #-}

postulate
  Char : Set
  String : Set
{-# BUILTIN STRING String #-}
{-# BUILTIN CHAR Char #-}

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


private
  primitive
    primStringAppend : String -> String -> String
    primCharToNat : Char -> Nat
    primCharEquality : Char -> Char -> Bool


_++_ : String → String → String
_++_ = primStringAppend

_>>_ : ∀ {A B} →  IO A → IO B → IO B
m1 >> m2 = m1 >>= λ _ → m2

_+_ : Nat -> Nat -> Nat
zero + y = y
suc x + y = suc (x + y)


data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : forall {n} (x : A) (xs : Vec A n) -> Vec A (suc n)

buildVec : Vec Nat 4
buildVec = 32 :: (12 :: (54 :: (23 :: [])))

vecToStr : forall {A m} -> (A -> String) -> Vec A m -> String
vecToStr f [] = "[]"
vecToStr f (x :: xs) = "[ " ++ ((f x) ++ ((v2s f xs) ++ "]"))
  where v2s : forall {A m} -> (A -> String) -> Vec A m -> String
        v2s f [] = ""
        v2s f (x :: xs) = ", " ++ ((f x) ++ (v2s f xs))

if_then_else : {a : Set} -> Bool -> a -> a -> a
if_then_else true a₁ b = a₁
if_then_else false a₁ b = b

_&&_ : Bool -> Bool -> Bool
true && b = b
false && b = false

main : IO Unit
main = putStrLn (vecToStr natToStr k)
  where k = if (true && true) then 23 :: (54 :: (234 :: (0 :: []))) else buildVec
