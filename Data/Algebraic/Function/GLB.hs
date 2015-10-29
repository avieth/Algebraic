{-|
Module      : Data.Algebraic.Function.GLB
Description : Infrastructure for combining F's of different parameters.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}

module Data.Algebraic.Function.GLB where

import GHC.TypeLits
import GHC.Exts (Constraint)
import Prelude hiding ((.), id)
import Control.Category
import Control.Arrow
import Data.Proxy
import Data.Functor.Identity
import Data.List.NonEmpty
import Data.Algebraic.Function

type family GLB (h :: * -> * -> *) (f :: * -> * -> *) :: * -> * -> * where
    GLB Bijection f = f
    GLB f Bijection = f
    GLB EmptyArrow f = EmptyArrow
    GLB f EmptyArrow = EmptyArrow
    GLB Injection Surjection = Function
    GLB Surjection Injection = Function
    GLB Function Injection = Function
    GLB Injection Function = Function
    GLB Function Surjection = Function
    GLB Surjection Function = Function
    GLB f f = f

type family GLBFold (hs :: [* -> * -> *]) :: * -> * -> * where
    GLBFold '[] = Bijection
    GLBFold (h ': hs) = GLB h (GLBFold hs)

class WitnessGLB h g where
    witnessGLB :: forall s t . Proxy g -> h s t -> (GLB h g) s t

instance
    ( WitnessGLBDisambiguated (GLBDisambiguator h g) h g
    ) => WitnessGLB h g
  where
    witnessGLB proxyG = witnessGLBDisambiguated (Proxy :: Proxy (GLBDisambiguator h g)) proxyG

type family GLBDisambiguator (h :: * -> * -> *) (g :: * -> * -> *) :: GLBDisambiguatorT where
    GLBDisambiguator Bijection f = BijectionLeft
    GLBDisambiguator f Bijection = BijectionRight
    GLBDisambiguator EmptyArrow f = EmptyLeft
    GLBDisambiguator f EmptyArrow = EmptyRight
    GLBDisambiguator f f = Same
    GLBDisambiguator f g = Known

data GLBDisambiguatorT where
    BijectionLeft :: GLBDisambiguatorT
    BijectionRight :: GLBDisambiguatorT
    EmptyLeft :: GLBDisambiguatorT
    EmptyRight :: GLBDisambiguatorT
    Same :: GLBDisambiguatorT
    Known :: GLBDisambiguatorT

class WitnessGLBDisambiguated d h g where
    witnessGLBDisambiguated :: Proxy d -> Proxy g -> h s t -> (GLB h g) s t

instance {-# OVERLAPS #-}
    ( GLB f f ~ f
    ) => WitnessGLBDisambiguated Same f f
  where
    witnessGLBDisambiguated _ _ = id

instance {-# OVERLAPS #-}
    ( Arrow f
    ) => WitnessGLBDisambiguated BijectionLeft Bijection f
  where
    witnessGLBDisambiguated _ _ = transBijection

instance {-# OVERLAPS #-}
    (
    ) => WitnessGLBDisambiguated BijectionRight f Bijection
  where
    witnessGLBDisambiguated _ _ = id

instance {-# OVERLAPS #-}
    (
    ) => WitnessGLBDisambiguated EmptyLeft EmptyArrow f
  where
    witnessGLBDisambiguated _ _ = transEmpty

instance
    (
    ) => WitnessGLBDisambiguated EmptyRight f EmptyArrow
  where
    witnessGLBDisambiguated _ _ = transEmpty

instance
    (
    ) => WitnessGLBDisambiguated Known Injection Surjection
  where
    witnessGLBDisambiguated _ _ = transInjectionFunction

instance
    (
    ) => WitnessGLBDisambiguated Known Surjection Injection
  where
    witnessGLBDisambiguated _ _ = transSurjectionFunction

instance
    (
    ) => WitnessGLBDisambiguated Known Function Injection
  where
    witnessGLBDisambiguated _ _ = id

instance
    (
    ) => WitnessGLBDisambiguated Known Injection Function
  where
    witnessGLBDisambiguated _ _ = transInjectionFunction

instance
    (
    ) => WitnessGLBDisambiguated Known Function Surjection
  where
    witnessGLBDisambiguated _ _ = id

instance
    (
    ) => WitnessGLBDisambiguated Known Surjection Function
  where
    witnessGLBDisambiguated _ _ = transSurjectionFunction

transBijection :: Arrow f => Bijection s t -> f s t
transBijection kl = arr (runIdentity . runKleisli kl)

transEmpty :: f s t -> EmptyArrow s t
transEmpty = const EmptyArrow

transInjectionFunction :: Injection s t -> Function s t
transInjectionFunction kl = Kleisli $ \s -> case runKleisli kl s of
    Just x -> [x]
    Nothing -> []

transSurjectionFunction :: Surjection s t -> Function s t
transSurjectionFunction kl = Kleisli $ toList . runKleisli kl

-- What a nightmare.
type Composable f1 f2 = (
      WitnessGLB f1 (GLB f2 f1)
    , WitnessGLB f2 (GLB f1 f2)
    , WitnessGLB f2 (GLB f2 f1)
    , WitnessGLB f1 (GLB f1 f2)
    , WitnessGLB f1 (GLB f2 (GLB f1 f2))
    , WitnessGLB f2 (GLB f1 (GLB f2 f1))
    , GLB f1 (GLB f2 f1) ~ GLB f2 f1
    , GLB f2 (GLB f1 (GLB f2 f1)) ~ GLB f1 (GLB f2 f1)
    , GLB f1 (GLB f2 (GLB f1 f2)) ~ GLB f2 (GLB f1 f2)
    , GLB f1 f2 ~ GLB f1 (GLB f2 (GLB f1 f2))
    , Category (GLB f2 (GLB f1 (GLB f2 f1)))
    , Category (GLB f1 f2)
    )

composeFs
    :: forall f1 g1 f2 g2 s t u .
       ( Composable f1 f2
       , Composable g1 g2
       )
    => F f2 g2 u t
    -> F f1 g1 s u
    -> F (GLB f2 f1) (GLB g2 g1) s t
composeFs left right = left' . right'
  where
    left' :: F (GLB f2 f1) (GLB g2 g1) u t
    left' = F (witnessGLB (Proxy :: Proxy (GLB f2 f1)) (to left))
              (witnessGLB (Proxy :: Proxy (GLB g2 g1)) (from left))
    right' :: F (GLB f2 f1) (GLB g2 g1) s u
    right' = F (witnessGLB (Proxy :: Proxy (GLB f2 f1)) (to right))
               (witnessGLB (Proxy :: Proxy (GLB g2 g1)) (from right))
(<.>)
    :: forall f1 g1 f2 g2 s t u .
       ( Composable f1 f2
       , Composable g1 g2
       )
    => F f2 g2 u t
    -> F f1 g1 s u
    -> F (GLB f2 f1) (GLB g2 g1) s t
(<.>) = composeFs
infixr 9 <.>
