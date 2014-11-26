module VecHS where


{-# IMPORT Nat #-}
---------------------
------ Prelude ------
---------------------

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ
{-# COMPILED_DATA ℕ Nat Zero Suc #-}
{-- BUILTIN NATURAL ℕ --}

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

three four five ten twelve thirteen fifty-four hundred fife-four-three two-three-four three-four-five three-five-four-one-three two-three-four-one-two thousand : ℕ
three = suc (suc (suc zero))
four = suc three
five = suc (suc three)
ten = suc (three * three)
twelve = three * (suc three)
thirteen = suc twelve
fifty-four = (five * ten) + four
hundred = ten * ten
fife-four-three = ((hundred * five) + (four * ten)) + three
two-three-four = ((suc (suc zero) * hundred) + (three * ten)) + four
three-four-five = ((three * hundred) + (ten * four)) + five
thousand = hundred * ten
three-five-four-one-three = ((((three * (ten * thousand)) + (five * thousand)) +
                                (four * hundred))
                               + ten)
                              + three
two-three-four-one-two = ((((suc (suc zero) * (ten * thousand)) + (three * thousand)) +
                             (four * hundred))
                            + ten)
                           + suc (suc zero)


-- correct result : 120060
compute : ℕ
compute = sum (vmap sum n)
  where m : Matrix ℕ three three
        m = Cons (Cons thirteen (Cons fifty-four (Cons fife-four-three Nil))) (Cons (Cons two-three-four (Cons zero (Cons twelve Nil))) (Cons (Cons three-four-five (Cons three-five-four-one-three (Cons two-three-four-one-two Nil))) Nil))
        g l n : Matrix ℕ three three
        g = madd (transpose (transpose m)) (transpose (madd m idMatrix))
        k = madd (madd g g) (madd g g)
        l = madd (madd k g) (madd g k)
        n = madd (madd l k) (madd k l)

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

--private
-- primitive
--  primCharToNat    : Char → ℕ
--  primCharEquality : Char → Char → Bool


data ⊤ : Set where
  tt : ⊤
{-# COMPILED_DATA ⊤ () () #-}

postulate
    IO : ∀ {l} -> Set l -> Set l

{-# IMPORT IO.FFI #-}
{-# COMPILED_TYPE IO IO.FFI.AgdaIO #-}
{-# BUILTIN IO IO #-}

postulate
    return  : ∀ {a} {A : Set a} -> A -> IO A
    _>>=_   : ∀ {a b} {A : Set a} {B : Set b} -> IO A -> (A -> IO B) -> IO B
    putStrLn : String -> IO ⊤

{-# COMPILED return (\_ _ -> return)    #-}
{-# COMPILED _>>=_ (\_ _ _ _ -> (>>=)) #-}
{-# COMPILED putStrLn putStrLn #-}


data List {a} (A : Set a) : Set a where
  [] : List A
  _∷_ : (x : A) (xs : List A) → List A

{-# BUILTIN LIST List #-}
{-# BUILTIN NIL [] #-}
{-# BUILTIN CONS _∷_ #-}
{-# IMPORT Data.FFI #-}
{-# COMPILED_DATA List Data.FFI.AgdaList [] (:) #-}


postulate
  primStringFromList   : (List Char) -> String
  natToStr             : ℕ -> String
--  seq : {A B : Set} → A -> B -> B

--{-# COMPILED seq (\_ _ a b -> seq a b) #-}
{-# COMPILED primStringFromList (\x -> x) #-}
{-# COMPILED natToStr showNat #-}
  
{-_>>_ : ∀ {A B} →  IO A → IO B → IO B
m₁ >> m₂ = m₁ >>= λ _ → m₂-}

main : IO ⊤
main = putStrLn (natToStr compute) -- >> return tt



