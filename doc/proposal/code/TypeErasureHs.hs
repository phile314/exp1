{-# LANGUAGE GADTs, NoGenericDeriving #-}

module TypeErasureHs where

data List' a where
  Nil :: List' a
  Cons :: a -> List' a -> List' a
