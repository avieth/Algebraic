{-|
Module      : Examples.Sum
Description : Example of a projection from a 2-element sum.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeOperators #-}

module Examples.Sum where

import Control.Arrow
import Data.Void
import Data.Algebraic.Index
import Data.Algebraic.Sum
import Data.Algebraic.Product
import Data.Algebraic.Function

makeVoid :: F Partial Bijection t Void
makeVoid = F fto ffrom
  where
    fto :: Partial t Void
    fto = Kleisli (\_ -> Nothing)
    ffrom :: Bijection Void t
    ffrom = arr absurd

selectFirst :: F Partial Bijection (s :+: t) s
selectFirst = eliminateSummand two <.> sumF (identity .*. makeVoid)

-- | runKleisli (to example) (inject two "foo") = Nothing
--   runKleisli (to example) (inject one (1 :: Int)) = Just 1
--   runIdentity . runKleisli (from example) :: Int -> (Int :+: String)
example :: F Partial Bijection (Int :+: String) Int
example = selectFirst
