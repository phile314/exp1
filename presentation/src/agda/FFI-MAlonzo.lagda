\begin{code}
------------------------------------------------------------------------
-- The Agda standard library
-- 
-- Primitive IO: simple bindings to Haskell types and functions
------------------------------------------------------------------------
module FFI-MAlonzo where
--open import Data.Char
--open import Data.String
--open import Foreign.Haskell
------------------------------------------------------------------------

\end{code}
\begin{code}
{-# IMPORT Data.List #-}

data List : (A : Set) -> Set where
  nil : ∀ {A} → List A
  cons : ∀ {A} → A → List A → List A
{-# COMPILED_DATA List Data.List nil cons #-}

postulate
  head : ∀ {A} → List A -> A
{-# COMPILED head Data.List.head #-}

\end{code}
