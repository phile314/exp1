\begin{code}
module AgdaIntro where

postulate
  DUMMY : {A : Set} → A

\end{code}

\begin{code}
data Nat : Set where
  zero : Nat
  succ : Nat → Nat
\end{code}

\begin{code}
data Vec : (A : Set) → (n : Nat) → Set₁ where
  nil  : ∀ {A} → Vec A zero
  cons : ∀ {A n} → A → Vec A n → Vec A (succ n)
\end{code}

\begin{code}
head1 : ∀ {A n} → Vec A n → A
head1 (cons x xs) = x
head1 nil = DUMMY
\end{code}

\begin{code}
head2 : ∀ {A n} → Vec A (succ n) → A
head2 (cons x xs) = x
\end{code}
