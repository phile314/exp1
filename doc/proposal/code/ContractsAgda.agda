module ContractsAgda where

data A : Set where
  test : A

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

data IsEven : (b : Nat) -> Set where
  zero : IsEven zero
  suc : {b : Nat} -> IsEven b -> IsEven (suc (suc b))

data bot : Set where

-- copied from Relation.Nullary.Core
infix 3 not_

not_ : ∀ {ℓ} → Set ℓ → Set ℓ
not P = P → bot

data Eq {A : Set} : (x : A) -> (y : A) -> Set where
  refl : (x₁ : A) -> Eq x₁ x₁



data Dec {p} (P : Set p) : Set p where
  yes : ( p :   P) -> Dec P
  no  : (np : not P) -> Dec P

isEven : (b : Nat) -> Set
isEven b = IsEven b

isEven? : (b : Nat) -> Dec (IsEven b)
isEven? zero = yes zero
isEven? (suc zero) = no \()
isEven? (suc (suc b)) with isEven? b
isEven? (suc (suc b)) | yes p = yes (suc p)
isEven? (suc (suc b)) | no np = no f
  where f : (x : IsEven (suc (suc b))) -> bot
        f (suc isb) = np isb

-- Encapsulates the proof if the contract is met.
-- I  : input value
-- O  : output value
-- PF : proof function. Computes the type of the proof object,
--      given the input value.
-- F  : The function to execute.
data Safe (I : Set) (O : Set) (PF : O -> Set) (F : I -> O) : Set where
  safe :  (i : I) -> (o : O) -> PF o -> Eq o (F i) -> Safe I O PF F

-- Internal (dangerous!) helper function.
postulate
  error : {a : Set} -> a

-- Computes the result type of a contract. Can also be filled in
-- automatically by Agda using C-c C-a.
assertT : {I : Set} {O : Set} -> (PF : O -> Set) -> (F : I -> O) -> Set
assertT {I} {O} PF F = (i : I) -> Safe I O PF F

-- Assert that a contract holds on a value. Either returns
-- the result together with the proof, or throws a runtime error.
assertV : {I : Set} {O : Set} -> (PF : O -> Set) -> (F : I -> O)
            -> ((o : O) -> (Dec (PF o))) -> assertT PF F
assertV PF F dec i with dec (F i)
assertV PF F dec i | yes p = safe i (F i) p (refl (F i))
assertV PF F dec i | no np = error

-- The dangerous function to call.
postulate 
  testDangerous : A -> Nat

-- Wrap the dangerous function.
testSafe : assertT isEven testDangerous
testSafe = assertV isEven testDangerous isEven?

-- Same as testSafe, but with explicit type signature.
testSafe2 : (x : A) -> Safe A Nat isEven testDangerous
testSafe2 = assertV isEven testDangerous isEven?

-- It is also possible to assert non-sense,
-- but impossible to give non-sense a valid type.
non-sense : {!!}
non-sense = assertV isEven (\x -> 1) isEven?

p : {!!}
p with testSafe test
p | safe i o x x₁ = {!!}

k : {!!}
k = assertV isEven (\x -> 10) isEven?

l : {!!}
l = assertV isEven (\x -> 1) isEven?

m : {!!}
m with k 10
m | safe i .10 x (refl .10) = {!!}

n : {!!}
n with l 1
n | safe i .1 x (refl .1) = {!x!}
