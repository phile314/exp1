\begin{code}
module NatOptim where

\end{code}

\begin{code}
data Nat : Set where
  zero : Nat
  succ : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

\end{code}
