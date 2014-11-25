\begin{code}
module AgdaIntro where


\end{code}

\begin{code}
data Nat : Set where
  zero : Nat
  succ : Nat → Nat

data Vec : (A : Set) → (n : Nat) → Set where
  nil  : ∀ {A} → Vec A zero
  cons : ∀ {A n} → A → Vec A n → Vec A (succ n)

head : ∀ {A n} → Vec A (succ n) → A
head (cons x xs) = x
\end{code}
