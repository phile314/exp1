module ClassAgda2 where

data Bool : Set where
  True : Bool
  False : Bool

primBoolEq : Bool -> Bool -> Bool
primBoolEq True y = y
primBoolEq False True = False
primBoolEq False False = True

-- Define class as record (datatype/postulate also possible)
record Eq (A : Set) : Set where
  field
    eq : A -> A -> Bool

-- Open the Eq record as class-like thing
open Eq {{...}}

-- Mark instances with the "instance" keyword
instance
  eqBool : Eq Bool
  eqBool = record { eq = primBoolEq }

-- The "eq" record member now gets the proper instance automatically
-- If more than one instance is found, which are not definitionally equal,
-- the type checker will complain.
test : Bool -> Bool
test b = eq b False

-- If we want to delay the choice of instance, an instance
-- argument can be used.
test2 : {A : Set} -> {{e : Eq A}} -> A -> A -> Bool
test2 a b = eq a b

-- The instance argument now gets filled in at the call site.
test3 : Bool
test3 = test2 False True

data HasDefault (A : Set) : Set where
  useImpl : A -> HasDefault A
  useDefault : HasDefault A

record Ord (A : Set) : Set where
  field
    eqInst : Eq A
    lteq' : HasDefault (A -> A -> Bool)
postulate lteqDef : {A : Set} -> A -> A -> Bool

lteq : {A : Set} {{e : Ord A}} -> A -> A -> Bool
lteq {{o}} with Ord.lteq' o
lteq | useImpl x  = x
lteq | useDefault = lteqDef


postulate primLteqBool : Bool -> Bool -> Bool

instance
  ordBool : Ord Bool
  ordBool = record { eqInst = eqBool ; lteq' = useImpl primLteqBool  }

test4 : Bool
test4 = {!ℕ!}


rnk2 : {A : Set} -> A -> ((B : Set) -> B -> A)
rnk2 = {!!}


data List (A : Set) : Set where
  nil : List A
  cons : A -> List A -> List A


f : (x : Set) -> Bool
f = λ x → True

f' : Bool
f' = True

m : Bool
m with f
... | sf = {!sf!}


