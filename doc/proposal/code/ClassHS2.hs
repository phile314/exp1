{-# LANGUAGE NoGenericDeriving #-}
module ClassHaskell where

class Eq2 a where
  eq :: a -> a -> Bool
  neq :: a -> a -> Bool
  neq a b = not $ eq a b

instance Eq2 Bool where
  eq a b = a == b

test :: Bool -> Bool
test a = eq a False

test2 :: (Eq2 a) => a -> a -> Bool
test2 a b = eq a b

test3 :: Bool
test3 = test2 False True
