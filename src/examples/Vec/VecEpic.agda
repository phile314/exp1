module VecEpic where



---------------------
------ Prelude ------
---------------------

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# COMPILED_EPIC zero primZero() #-}
{-# COMPILED_EPIC suc  (x : Any) -> primSuc(x) #-}

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

_*_ : ℕ → ℕ → ℕ
zero  * n = zero
suc m * n = n + (m * n)

data Vec (a : Set) : ℕ -> Set where
  Nil : Vec a zero
  Cons : {n : ℕ} -> (x : a) -> (xs : Vec a n) -> Vec a (suc n)



head : {a : Set} {n : ℕ}-> Vec a (suc n) -> a
head (Cons x xs) = x

append : {a : Set} {n m : ℕ} -> Vec a n -> Vec a m -> Vec a (n + m)
append Nil ys = ys
append (Cons x xs) ys = Cons x (append xs ys)

data _==_ {a : Set} (x : a) : a -> Set where
  Refl : x == x


----------------------
----- Exercise 1 -----
----------------------

--Show that the Vec a n type is applicative

pure : {n : ℕ} {a : Set} -> a -> Vec a n
pure {zero} x = Nil
pure {suc n} x = Cons x (pure x)

_<*>_ : {a b : Set} {n : ℕ} -> Vec (a -> b) n -> Vec a n -> Vec b n
Nil <*> xs = Nil
Cons x fs <*> Cons x₁ xs = Cons (x x₁) (fs <*> xs)

vmap : {a b : Set} {n : ℕ} -> (a -> b) -> Vec a n -> Vec b n
vmap f Nil = Nil
vmap f (Cons x xs) = Cons (f x) (vmap f xs)

----------------------
----- Exercise 2 -----
----------------------

-- Using the Vector definitions, define a type for matrices;
-- matrix addition; the identity matrix; and matrix transposition.

Matrix : Set -> ℕ -> ℕ -> Set
Matrix a n m = Vec (Vec a m) n

-- Define matrix addition
madd : {n m : ℕ} -> Matrix ℕ m n -> Matrix ℕ m n -> Matrix ℕ m n
madd a b = vmap (λ x → \y -> vmap _+_ x <*> y) a <*> b

-- Define the identity matrix
idMatrix : {n : ℕ} -> Matrix ℕ n n
idMatrix {zero} = Nil
idMatrix {suc n} = Cons (Cons (suc zero) (pure n)) (vmap (λ x → Cons zero x) idMatrix)

-- Define matrix transposition
tail : {n : ℕ} {a : Set} -> Vec a (suc n) -> Vec a n
tail (Cons x x₁) = x₁
transpose : {n m : ℕ} {a : Set} -> Matrix a m n -> Matrix a n m
transpose {zero} {zero} a₁ = Nil
transpose {zero} {suc m} {a} x = Nil
transpose {suc n} {zero} a₁ = pure Nil
transpose {suc n} {suc m} {a} (Cons x₁ x₂) with vmap head (Cons x₁ x₂) 
... | vm = Cons vm (vmap (λ p → λ q → Cons p q) (tail x₁) <*> transpose (vmap tail x₂))

sum : {n : ℕ} -> Vec ℕ n -> ℕ
sum Nil = zero
sum (Cons x v) = x + (sum v)

t1 = suc zero
t2 = suc t1
t3 = suc t2
t4 = suc t3
t5 = suc t4
t10 = t5 + t5
t11 = suc t10
t12 = suc t11
t13 = suc t12
t20 = t10 + t10
t30 = t20 + t10
t40 = t30 + t10
t50 = t40 + t10
t54 = t50 + t4
t100 = t50 + t50
t200 = t50 + t50
t234 = t200 + (t30 + t4)
t345 = t200 + (t100 + (t40 + t5))
t400 = t200 + t200
t543 = t400 + (t100 + (t40 + t3))
t800 = t400 + t400
t23412 = ((t100 * t10) * (t20 + t3)) + (t400 + t12)
t35413 = ((t100 * t10) * (t30 + t5)) + (t400 + t13)

-- correct result : 120060
compute : ℕ
compute = sum (vmap sum g)
  where m : Matrix ℕ t3 t3
        m = Cons (Cons t13 (Cons t54 (Cons t543 Nil))) (Cons (Cons t234 (Cons zero (Cons t12 Nil))) (Cons (Cons t345 (Cons t35413 (Cons t23412 Nil))) Nil))
        g : Matrix ℕ t3 t3
        g = madd (transpose (transpose m)) (transpose (madd m idMatrix))


---------------------
------ MAIN    ------
---------------------


postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

postulate
  Char : Set

{-# BUILTIN CHAR Char #-}
{-# COMPILED_TYPE Char Char #-}

private
 primitive
  primCharToNat    : Char → ℕ
--  primCharEquality : Char → Char → Bool


data ⊤ : Set where
  tt : ⊤

postulate
    IO      : Set -> Set
    return  : {A : Set} -> A -> IO A
    _>>=_   : {A B : Set} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO ⊤

{-# COMPILED_EPIC return (u1 : Unit, a : Any) -> Any = ioreturn(a) #-}
{-# COMPILED_EPIC _>>=_ (u1 : Unit, u2 : Unit, x : Any, f : Any) -> Any = iobind(x,f) #-}
{-# COMPILED_EPIC putStrLn (a : String , u : Unit) -> Unit = putStrLn(a) #-}

{- data List {a} (A : Set a) : Set a where
  []  : List A
  _∷_ : (x : A) (xs : List A) → List A -}

postulate
  List : Set -> Set

--{-# BUILTIN LIST List #-}
--{-# COMPILED_TYPE List List #-}

postulate
  primNil    : (a : Set) → List a
  primCons   : (a : Set) → a → List a → List a
{-# COMPILED_EPIC primNil (u : Unit) -> Any = primNil() #-}
{-# COMPILED_EPIC primCons (u : Unit, x : Any, xs : Any) -> Any = primCons(x,xs) #-}

--primitive primStringFromList :  List Char -> String
postulate
  primStringFromList   : (List Char) -> String
  bigToStr 	       : ℕ -> String

{-# COMPILED_EPIC primStringFromList (l : Any) -> String = primStringFromList(l) #-}
{-# COMPILED_EPIC bigToStr (x : BigInt) -> String = bigToStr(x) #-}
  
_>>_ : ∀ {A B} →  IO A → IO B → IO B
m₁ >> m₂ = m₁ >>= λ _ → m₂

main : IO ⊤
main = putStrLn (bigToStr compute) >> return tt



