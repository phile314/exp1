module UnicodeTest where

data ℕ =
  Suc ℕ | Zero
  deriving (Show)

--data Nat =
--  Suc Nat | Zero

toℕ :: Integer -> ℕ
toℕ 0 = Zero
toℕ i = Suc (toℕ (i - 1))

main :: IO ()
main = putStrLn $ show $ toℕ 10
