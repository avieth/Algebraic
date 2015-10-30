{-|
Module      : Examples.Tuple
Description : An example of tuple projection.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Examples.Tuple where

import Prelude hiding ((.), id)
import Control.Arrow
import Control.Category
import Data.List.NonEmpty
import Data.Algebraic.Index
import Data.Algebraic.Product
import Data.Algebraic.Function

-- | In order to make a total surjection onto (), we must be able to enumerate
--   the entire domain type, as the entire type is the preimage of ().
terminalSurjection
    :: forall a .
       ( Enum a, Bounded a )
    => F Total Surjection a ()
terminalSurjection = F fto ffrom
  where
    fto :: Total a ()
    fto = arr (const ())
    ffrom :: Surjection () a
    ffrom = Kleisli (\() -> minBound :| [succ minBound..])

-- | If the domain is not enumerable and bounded, we can't obtain a surjection,
--   so we must settle for an F which is not reversible.
terminal :: F Total EmptyArrow a ()
terminal = F fto ffrom
  where
    fto :: Total a ()
    fto = arr (const ())
    ffrom :: EmptyArrow () a
    ffrom = EmptyArrow

identity :: F Total Bijection a a
identity = id

projectFirst :: (Enum b, Bounded b) => F Total Surjection (a :*: b) a
projectFirst = eliminateTerm two <.> productF (identity .*. terminalSurjection)

-- | runKleisli (from example) 1 = (1, True) :| (1, False)
example :: F Total Surjection (Int :*: Bool) Int
example = projectFirst
