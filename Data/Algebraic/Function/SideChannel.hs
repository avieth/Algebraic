{-|
Module      : Data.Algebraic.Function.SideChannel
Description : Definition of arrows with side channels.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Algebraic.Function.SideChannel (

      SideChannel(..)

    ) where

import Prelude hiding ((.), id, (+), (-))
import Control.Category
import Control.Arrow
import Data.Algebraic.Function

-- | Take any arrow and throw on some extra data.
newtype SideChannel a f s t = SideChannel {
      runSideChannel :: f (s, a) (t, a)
    }

instance Category f => Category (SideChannel a f) where
    id = SideChannel id
    x . y = SideChannel $ runSideChannel x . runSideChannel y

instance Arrow f => Arrow (SideChannel a f) where
    arr = SideChannel . arr . first
    first f = SideChannel $ arr (\((t, m), c) -> ((t, c), m))
                          . first (runSideChannel f)
                          . arr (\((t, m), c) -> ((t, c), m))

instance ArrowChoice f => ArrowChoice (SideChannel a f) where
    left f = SideChannel $ arr after
                         . left (runSideChannel f)
                         . arr before
      where
        before :: forall s c a . (Either s c, a) -> Either (s, a) (c, a)
        before (sum, a) = case sum of
            Left s -> Left (s, a)
            Right c -> Right (c, a)
        after :: forall s c a . Either (s, a) (c, a) -> (Either s c, a)
        after sum = case sum of
            Left (s, a) -> (Left s, a)
            Right (c, a) -> (Right c, a)

instance ArrowApply f => ArrowApply (SideChannel monoid f) where
    app = SideChannel $ proc ((f, x), m) -> do (y, m') <- app -< (runSideChannel f, (x, m))
                                               returnA -< (y, m')

instance Arrow f => Functor (SideChannel monoid f s) where
    fmap f = SideChannel . (.) (arr (\(x, m) -> (f x, m))) . runSideChannel

instance Arrow f => Applicative (SideChannel monoid f s) where
    pure x = SideChannel (arr (\(s, m) -> (x, m)))
    mf <*> mx = SideChannel $ proc (s, m) -> do (f, m') <- runSideChannel mf -< (s, m)
                                                (x, m'') <- runSideChannel mx -< (s, m')
                                                returnA -< (f x, m'')

instance ArrowApply f => Monad (SideChannel monoid f s) where
    return = pure
    mx >>= k = SideChannel $ proc (s, m) -> do (x, m') <- runSideChannel mx -< (s, m)
                                               (y, m'') <- app -< (runSideChannel (k x), (s, m'))
                                               returnA -< (y, m'')

--   arrowHomomorphism (arr f)
-- = SideChannel $ first (arrowHomomorphism (arr f))  ; by definition
-- = SideChannel $ first (arr f)                      ; by assumption
-- = arr f                                            ; by definition
--
--   arrowHomomorphism (first f)
-- = SideChannel $ first (arrowHomomorphism (first f))  ; by definition
-- = SideChannel $ first (first f)                      ; by assumption
-- = first f
--
--   arrowHomomorphism f . arrowHomomorphism g
-- = (SideChannel (first (arrowHomomorphism f))) . (SideChannel (first (arrowHomomorphism g)))
-- = SideChannel $ first (arrowHomomorphism f) . first (arrowHomomorphism g)
-- = SideChannel $ first (arrowHomomorphism f . arrowHomomorphism g)
-- = SideChannel $ first (arrowHomomorphism (f . g))
-- = arrowHomomorphism (f . g)
--
--   arrowHomomorphism id
-- = SideChannel $ first (arrowHomomorphism id)
-- = SideChannel $ first id
-- = id
instance {-# OVERLAPS #-}
    ( ArrowHomomorphism f g
    , Arrow g
    ) => ArrowHomomorphismTyped AHParticular f (SideChannel a g)
  where
    arrowHomomorphismTyped _ f = SideChannel $ first (arrowHomomorphism f)

-- TODO check this one. Is it really a homomorphism?
instance {-# OVERLAPS #-}
    ( ArrowHomomorphism f g
    , Arrow g
    , Monoid a
    ) => ArrowHomomorphismTyped AHParticular (SideChannel a f) g
  where
    arrowHomomorphismTyped _ f = arr fst
                               . arrowHomomorphism (runSideChannel f)
                               . arr (\x -> (x, mempty))

--type instance ArrowGLBOrderT (SideChannel a f) = ArrowGLBOrderT f 
--type instance ArrowHomomorphismGreatestLowerBound (SideChannel a f) g =
--    SideChannel a (ArrowHomomorphismGreatestLowerBound f g)
