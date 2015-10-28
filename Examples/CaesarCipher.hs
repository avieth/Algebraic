{-|
Module      : Examples.CaesarCipher
Description : Definition of a cipher using Data.Algebra.Function
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

module Examples.CaesarCipher where

import Prelude hiding ((.), id, (+), (-))
import Control.Category
import Control.Arrow
import Numeric.Additive.Group
import Numeric.Additive.Class
import Data.Algebraic.Function

-- | For any group, adding an element gives a total bijection, since it
--   is essentially a permutation of the group elements.
--   A note on the program text: the (+) and (-) functions here are from
--   the algebra package. (-) comes from the Group class, and (+) from the
--   Additive class.
plus :: (Group a) => a -> F Total Bijection a a
plus x = F (arr ((+) x)) (arr (\y -> y - x))

-- | Flipping @plus@ around, we get its inverse, @minus@. Recall that
--   Total = Bijection = Kleisli Identity.
minus :: (Group a) => a -> F Total Bijection a a
minus x = opposite (plus x)

-- | The classic Caesar Cipher.
--
--     @
--       encode :: Group g => g -> [g] -> [g]
--       encode shift = runIdentity (runKleisli (to (caesarCipher shift)))
--
--       decode :: Group g => g -> [g] -> [g]
--       decode shift = runIdentity (runKleisli (from (caesarCipher shift)))
--     @
--
--   where
--
--     @
--       decode shift . encode shift = id
--     @
--
caesarCipher :: (Group g) => g -> F Total Bijection [g] [g]
caesarCipher = throughTraversable . plus
