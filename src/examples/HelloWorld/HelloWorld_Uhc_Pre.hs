{-# LANGUAGE NoGenericDeriving #-}
module HelloWorld_Uhc_Pre where

import Prelude (seq, Show (..), String, IO (..), Num (..), (.))

import qualified Prelude as P

-- not sure what the exact core representation of () is (I get {CTag Rec}
data Unit = TT
fixMain :: IO Unit -> IO ()
fixMain t = t P.>> return ()

-- Pull in required code, use `seq` to avoid dead-code elimination.
main :: IO ()
main = fixMain `seq` TT `seq` () `seq` P.putStrLn `seq` P.error `seq` ((>>=) :: IO a -> (a -> IO b) -> IO b) `seq` (return :: a -> IO a) `seq` return ()

-- remove class constraints from the functions

return :: a -> IO a
return = P.return

(>>=) :: IO a -> (a -> IO b) -> IO b
a >>= b = a P.>>= b
