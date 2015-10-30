{-|
Module      : Data.Algebraic.Function
Description : Definition of the F type to represent functions.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LiberalTypeSynonyms #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FunctionalDependencies #-}

module Data.Algebraic.Function (

      F(..)
    , GLB
    , GLBFold
    , WitnessGLB
    , witnessGLB
    , Composable
    , identity
    , fcompose
    , (<.>)
    , Total
    , Multi
    , Partial
    , Bijection
    , Injection
    , Surjection
    , Function
    , EmptyArrow(..)
    , opposite
    , ProductTos
    , ProductFroms
    , ProductF
    , productF
    , SumF
    , sumF
    , SequenceProduct
    , sequenceProduct
    , thru
    , pass
    , known
    , forget
    , throughTraversable
    , eliminateTerm
    , eliminateSummand
    , introduceTerm
    , introduceSummand
    , swapTerms
    , swapSummands
    , TotalBijectionOfUnitProduct
    , totalBijectionOfUnitProduct
    , TotalSurjectionOfHomogeneousSum
    , totalSurjectionOfHomogeneousSum
    , TotalInjectionOfSummand
    , totalInjectionOfSummand
    , HomogeneousSumImage
    , homogeneousSumImage
    , HomogeneousSumPreimage
    , homogeneousSumPreimage
    , homogeneousSumIndexedSurjection

    , disassembleProduct
    , disassembleSum
    , useBottomOfProduct
    , useBottomOfSum
    , reassembleProduct
    , reassembleSum

    ) where

import Prelude hiding ((.), id, (+), (-))
import GHC.TypeLits
import Control.Category
import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Proxy
import Data.Void
import Data.Semigroup ((<>), Semigroup)
import Data.Functor.Identity
import Data.List.NonEmpty
import Numeric.Additive.Group
import Numeric.Additive.Class
import Data.Algebraic.Index
import Data.Algebraic.Order
import Data.Algebraic.Product
import Data.Algebraic.Sum

-- | Not a Monad, not an Arrow, not even a Functor!
data F f g a b = F {
      to :: f a b
    , from :: g b a
    }

instance (Category f, Category g) => Category (F f g) where
    id = F id id
    x . y = F (to x . to y) (from y . from x)

instance (Category f, Category g) => Monoid (F f g s s) where
    mempty = id
    mappend = (.)

identity :: F Total Bijection s s
identity = id

-- Here we have a partial order.
--
--                    Kleisli Identity
--                ^                      ^
--               /                        \
--              /                          \
--             /                            \
--          Kleisli Maybe          Kleisli NonEmpty
--            ^         ^          ^         ^
--            |          \        /          |
--            |          Kleisli []          |
--            |                              |
--            \             ^                /
--             \            |               /
--              \                          /
--                     EmptyArrow
--
-- where x < y means that there is an arrow homomorphism from y to x.
type Total = Kleisli Identity
type Partial = Kleisli Maybe
type Multi = Kleisli NonEmpty
type Bijection = Kleisli Identity
type Injection = Kleisli Maybe
type Surjection = Kleisli NonEmpty
type Function = Kleisli []

data EmptyArrow s t = EmptyArrow

instance Category EmptyArrow where
    id = EmptyArrow
    _ . _ = EmptyArrow

instance Arrow EmptyArrow where
    arr _ = EmptyArrow
    first _ = EmptyArrow

-- | The greatest lower bound is a commutative thing. We present this:
--
--                     Kleisli Identity |Kleisli Maybe   |Kleisli NonEmpty|Kleisli []|EmptyArrow
--                   +--------------------------------------------------------------------------
--   Kleisli Identity| Kleisli Identity |Kleisli Maybe   |Kleisli NonEmpty|Kleisli []|EmptyArrow
--   Kleisli Maybe   | Kleisli Maybe    |Kleisli Maybe   |Kleisli []      |Kleisli []|EmptyArrow
--   Kleisli NonEmpty| Kleisli NonEmpty |Kleisli NonEmpty|Kleisli NonEmpty|Kleisli []|EmptyArrow
--   Kleisli []      | Kleisli []       |Kleisli []      |Kleisli []      |Kleisli []|EmptyArrow
--   EmptyArrow      | EmptyArrow       |EmptyArrow      |EmptyArrow      |EmptyArrow|EmptyArrow
--
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

-- | Fold a list of types using GLB.
type family GLBFold (hs :: [* -> * -> *]) :: * -> * -> * where
    GLBFold '[] = Bijection
    GLBFold (h ': hs) = GLB h (GLBFold hs)

-- | Proof of the GLB type family clauses.
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

-- | Like WitnessGLB but with an extra parameter to prevent overlap.
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

fcompose
    :: forall f1 g1 f2 g2 s t u .
       ( Composable f1 f2
       , Composable g1 g2
       )
    => F f2 g2 u t
    -> F f1 g1 s u
    -> F (GLB f2 f1) (GLB g2 g1) s t
fcompose left right = left' . right'
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
(<.>) = fcompose
infixr 9 <.>

-- | We get a Functor instance only if we have no obligation to give a
--   meaningful opposite arrow.
instance Arrow f => Functor (F f EmptyArrow s) where
    fmap f x = F (to x >>> arr f) EmptyArrow

-- | We get an Applicative instance only if we have no obligation to give a
--   meaningful opposite arrow.
instance Arrow f => Applicative (F f EmptyArrow s) where
    pure x = F (arr (const x)) EmptyArrow
    mf <*> mx = F fto EmptyArrow
      where
        fto = proc y -> do f <- to mf -< y
                           x <- to mx -< y
                           returnA -< f x

-- | We get a Monad instance only if we have no obligation to give a
--   meaningful opposite arrow.
instance ArrowApply f => Monad (F f EmptyArrow s) where
    return = pure
    mx >>= k = F fto EmptyArrow
      where
        fto = proc y -> do z <- to mx -< y
                           w <- app -< (to (k z), y)
                           returnA -< w

opposite :: F g h s t -> F h g t s
opposite f = F (from f) (to f)

-- | Instances of this class follow the IntroduceTerm family clauses, but
--   with () as the thing being introduced, which is why we get a total
--   bijection.
class IntroduceTermF product idx where
    introduceTerm :: Index idx -> F Total Bijection product (IntroduceTerm () product idx)

instance {-# OVERLAPS #-}
    (
    ) => IntroduceTermF (p :*: rest) 1
  where
    introduceTerm _ = F fto ffrom
      where
        fto :: Total (p :*: rest) (() :*: p :*: rest)
        fto = arr (\prod -> Product ((), prod))
        ffrom :: Bijection (() :*: p :*: rest) (p :*: rest)
        ffrom = arr (\(Product ((), rest)) -> rest)

instance {-# OVERLAPS #-}
    ( IntroduceTerm () rest 1 ~ (() :*: rest)
    , IntroduceTermF rest 1
    ) => IntroduceTermF (p :*: rest) 2
  where
    introduceTerm _ = reassembleProduct id
                    . useBottomOfProduct (introduceTerm (Index :: Index 1))
                    . disassembleProduct

instance {-# OVERLAPS #-}
    ( IntroduceTerm () (p :*: rest) n ~ (p :*: IntroduceTerm () rest (n - 1))
    , IntroduceTermF rest (n - 1)
    ) => IntroduceTermF (p :*: rest) n
  where
    introduceTerm _ = reassembleProduct id
                    . useBottomOfProduct (introduceTerm (Index :: Index (n - 1)))
                    . disassembleProduct

instance {-# OVERLAPS #-}
    ( IntroduceTerm () p 2 ~ (p :*: ())
    ) => IntroduceTermF p 2
  where
    introduceTerm _ = F fto ffrom
      where
        fto :: Total p (p :*: ())
        fto = arr (\p -> Product (p, ()))
        ffrom :: Bijection (p :*: ()) p
        ffrom = arr (\(Product (p, ())) -> p)

instance {-# OVERLAPS #-}
    ( IntroduceTerm () p 1 ~ (() :*: p)
    ) => IntroduceTermF p 1
  where
    introduceTerm proxyIdx = F fto ffrom
      where
        fto :: Total p (() :*: p)
        fto = arr (\p -> Product ((), p))
        ffrom :: Bijection (() :*: p) p
        ffrom = arr (\(Product ((), p)) -> p)


class IntroduceSummandF sum idx where
    introduceSummand :: Index idx -> F Total Bijection sum (IntroduceSummand Void sum idx)

instance {-# OVERLAPS #-}
    (
    ) => IntroduceSummandF (p :+: rest) 1
  where
    introduceSummand _ = F fto ffrom
      where
        fto :: Total (p :+: rest) (Void :+: p :+: rest)
        fto = arr (\sum -> Sum (Right sum))
        ffrom :: Bijection (Void :+: p :+: rest) (p :+: rest)
        ffrom = arr (\(Sum (Right sum)) -> sum)

instance {-# OVERLAPS #-}
    ( IntroduceSummand Void rest 1 ~ (Void :+: rest)
    , IntroduceSummandF rest 1
    ) => IntroduceSummandF (p :+: rest) 2
  where
    introduceSummand _ = reassembleSum id
                       . useBottomOfSum (introduceSummand (Index :: Index 1))
                       . disassembleSum

instance {-# OVERLAPS #-}
    ( IntroduceSummand Void (p :+: rest) n ~ (p :+: IntroduceSummand Void rest (n - 1))
    , IntroduceSummandF rest (n - 1)
    ) => IntroduceSummandF (p :+: rest) n
  where
    introduceSummand _ = reassembleSum id
                       . useBottomOfSum (introduceSummand (Index :: Index (n - 1)))
                       . disassembleSum

instance {-# OVERLAPS #-}
    ( IntroduceSummand Void p 2 ~ (p :+: Void)
    ) => IntroduceSummandF p 2
  where
    introduceSummand _ = F fto ffrom
      where
        fto :: Total p (p :+: Void)
        fto = arr (\p -> Sum (Left p))
        ffrom :: Bijection (p :+: Void) p
        ffrom = arr (\(Sum (Left p)) -> p)

instance {-# OVERLAPS #-}
    ( IntroduceSummand Void p 1 ~ (Void :+: p)
    ) => IntroduceSummandF p 1
  where
    introduceSummand _ = F fto ffrom
      where
        fto :: Total p (Void :+: p)
        fto = arr (\p -> (Sum (Right p)))
        ffrom :: Bijection (Void :+: p) p
        ffrom = arr (\(Sum (Right (p))) -> p)


-- | Instances of this class follow the EliminateTerm family clauses, but with
--   () as the thing being eliminated.
class EliminateTermF product idx where
    eliminateTerm :: Index idx -> F Total Bijection product (EliminateTerm product idx)

instance {-# OVERLAPS #-}
    (
    ) => EliminateTermF (() :*: rest) 1
  where
    eliminateTerm _ = F fto ffrom
      where
        fto :: Total (() :*: rest) rest
        fto = arr (\(Product ((), rest)) -> rest)
        ffrom :: Bijection rest (() :*: rest)
        ffrom = arr (\rest -> Product ((), rest))

-- This instance is to avoid overlap problems.
instance {-# OVERLAPS #-}
    (
    ) => EliminateTermF (() :*: q :*: rest) 1
  where
    eliminateTerm _ = F fto ffrom
      where
        fto :: Total (() :*: q :*: rest) (q :*: rest)
        fto = arr (\(Product ((), qrest)) -> qrest)
        ffrom :: Bijection (q :*: rest) (() :*: q :*: rest)
        ffrom = arr (\qrest -> Product ((), qrest))

instance {-# OVERLAPS #-}
    ( EliminateTerm (p :*: q :*: rest) n ~ (p :*: EliminateTerm (q :*: rest) (n - 1))
    , EliminateTermF (q :*: rest) (n - 1)
    ) => EliminateTermF (p :*: q :*: rest) n
  where
    eliminateTerm _ = reassembleProduct id
                    . useBottomOfProduct (eliminateTerm (Index :: Index (n - 1)))
                    . disassembleProduct

instance {-# OVERLAPS #-}
    (
    ) => EliminateTermF (p :*: ()) 2
  where
    eliminateTerm _ = F fto ffrom
      where
        fto :: Total (p :*: ()) p
        fto = arr (\(Product (p, ())) -> p)
        ffrom :: Bijection p (p :*: ())
        ffrom = arr (\p -> Product (p, ()))

instance {-# OVERLAPS #-}
    ( (EliminateTerm (p :*: rest) n) ~ (p :*: EliminateTerm rest (n - 1))
    , EliminateTermF rest (n - 1)
    ) => EliminateTermF (p :*: rest) n
  where
    eliminateTerm _ = reassembleProduct id
                    . useBottomOfProduct (eliminateTerm (Index :: Index (n - 1)))
                    . disassembleProduct

instance {-# OVERLAPS #-}
    (
    ) => EliminateTermF () 1
  where
    eliminateTerm _ = F returnA returnA


class EliminateSummandF sum idx where
    eliminateSummand :: Index idx -> F Total Bijection sum (EliminateSummand sum idx)

instance {-# OVERLAPS #-}
    (
    ) => EliminateSummandF (Void :+: rest) 1
  where
    eliminateSummand _ = F fto ffrom
      where
        -- Here we can ignore the Left case, since there couldn't possibly
        -- be a Void.
        fto :: Total (Void :+: rest) rest
        fto = arr (\(Sum (Right rest)) -> rest)
        ffrom :: Bijection rest (Void :+: rest)
        ffrom = arr (\rest -> Sum (Right rest))

-- This instance is to avoid overlap problems.
instance {-# OVERLAPS #-}
    (
    ) => EliminateSummandF (Void :+: q :+: rest) 1
  where
    eliminateSummand _ = F fto ffrom
      where
        fto :: Total (Void :+: q :+: rest) (q :+: rest)
        fto = arr (\(Sum (Right qrest)) -> qrest)
        ffrom :: Bijection (q :+: rest) (Void :+: q :+: rest)
        ffrom = arr (\qrest -> Sum (Right qrest))

instance {-# OVERLAPS #-}
    ( EliminateSummand (p :+: q :+: rest) n ~ (p :+: EliminateSummand (q :+: rest) (n - 1))
    , EliminateSummandF (q :+: rest) (n - 1)
    ) => EliminateSummandF (p :+: q :+: rest) n
  where
    eliminateSummand _ = reassembleSum id
                       . useBottomOfSum (eliminateSummand (Index :: Index (n - 1)))
                       . disassembleSum

instance {-# OVERLAPS #-}
    (
    ) => EliminateSummandF (p :+: Void) 2
  where
    eliminateSummand _ = F fto ffrom
      where
        fto :: Total (p :+: Void) p
        fto = arr (\(Sum (Left p)) -> p)
        ffrom :: Bijection p (p :+: Void)
        ffrom = arr (\p -> Sum (Left p))

instance {-# OVERLAPS #-}
    ( (EliminateSummand (p :+: rest) n) ~ (p :+: EliminateSummand rest (n - 1))
    , EliminateSummandF rest (n - 1)
    ) => EliminateSummandF (p :+: rest) n
  where
    eliminateSummand _ = reassembleSum id
                       . useBottomOfSum (eliminateSummand (Index :: Index (n - 1)))
                       . disassembleSum

instance {-# OVERLAPS #-}
    (
    ) => EliminateSummandF Void 1
  where
    eliminateSummand _ = F returnA returnA


class SwapTermsF product idx1 idx2 where
    swapTerms
        :: Index idx1
        -> Index idx2
        -> F Total Bijection product (SwapTerms product idx1 idx2)

instance {-# OVERLAPS #-}
    (
    ) => SwapTermsF p n n
  where
    swapTerms _ _ = id

-- This instance is to avoid overlap problems.
instance {-# OVERLAPS #-}
    (
    ) => SwapTermsF (p :*: q) n n
  where
    swapTerms _ _ = id

-- This instance is to avoid overlap problems.
instance {-# OVERLAPS #-}
    (
    ) => SwapTermsF (p :*: q :*: r) n n
  where
    swapTerms _ _ = id

instance {-# OVERLAPS #-}
    (   (SwapTerms (p :*: q :*: r) idx1 idx2)
      ~ (SwapTermsNormalize (p :*: q :*: r) idx1 idx2 (CmpNat idx1 idx2))
    , SwapTermsNormalizeF (p :*: q :*: r) idx1 idx2 (CmpNat idx1 idx2)
    ) => SwapTermsF (p :*: q :*: r) idx1 idx2
  where
    swapTerms proxyIdx1 proxyIdx2 = swapTermsNormalize proxyIdx1 proxyIdx2 (Proxy :: Proxy (CmpNat idx1 idx2))

instance {-# OVERLAPS #-}
    ( SwapTerms (p :*: q) 1 2 ~ (q :*: p)
    ) => SwapTermsF (p :*: q) 1 2
  where
    swapTerms _ _ = F fto ffrom
      where
        fto :: Total (p :*: q) (q :*: p)
        fto = arr (\(Product (p, q)) -> Product (q, p))
        ffrom :: Total (q :*: p) (p :*: q)
        ffrom = arr (\(Product (q, p)) -> Product (p, q))

-- This instance is to avoid overlap problems.
instance {-# OVERLAPS #-}
    ( SwapTerms (p :*: q :*: r) 1 2 ~ (q :*: p :*: r)
    ) => SwapTermsF (p :*: q :*: r) 1 2
  where
    swapTerms _ _ = F fto ffrom
      where
        fto :: Total (p :*: q :*: r) (q :*: p :*: r)
        fto = arr (\(Product (p, Product (q, r))) -> Product (q, Product (p, r)))
        ffrom :: Total (q :*: p :*: r) (p :*: q :*: r)
        ffrom = arr (\(Product (q, Product (p, r))) -> Product (p, Product (q, r)))

instance {-# OVERLAPS #-}
    ( SwapTerms (p :*: q) 2 1 ~ (q :*: p)
    ) => SwapTermsF (p :*: q) 2 1
  where
    swapTerms _ _ = F fto ffrom
      where
        fto :: Total (p :*: q) (q :*: p)
        fto = arr (\(Product (p, q)) -> Product (q, p))
        ffrom :: Total (q :*: p) (p :*: q)
        ffrom = arr (\(Product (q, p)) -> Product (p, q))

-- This instance is to avoid overlap problems.
instance {-# OVERLAPS #-}
    ( SwapTerms (p :*: q :*: r) 2 1 ~ (q :*: p :*: r)
    ) => SwapTermsF (p :*: q :*: r) 2 1
  where
    swapTerms _ _ = F fto ffrom
      where
        fto :: Total (p :*: q :*: r) (q :*: p :*: r)
        fto = arr (\(Product (p, Product (q, r))) -> Product (q, Product (p, r)))
        ffrom :: Total (q :*: p :*: r) (p :*: q :*: r)
        ffrom = arr (\(Product (q, Product (p, r))) -> Product (p, Product (q, r)))

class SwapTermsNormalizeF product (idx1 :: Nat) (idx2 :: Nat) (order :: Ordering) where
    swapTermsNormalize
        :: Index idx1
        -> Index idx2
        -> Proxy order
        -> F Total Bijection product (SwapTermsNormalize product idx1 idx2 order)

instance {-# OVERLAPS #-}
    ( SwapTerms_F product idx1 idx2
    ) => SwapTermsNormalizeF product idx1 idx2 LT
  where
    swapTermsNormalize proxyIdx1 proxyIdx2 _ = swapTerms_ proxyIdx1 proxyIdx2

instance {-# OVERLAPS #-}
    ( SwapTerms_F product idx2 idx1
    ) => SwapTermsNormalizeF product idx1 idx2 GT
  where
    swapTermsNormalize proxyIdx1 proxyIdx2 _ = swapTerms_ proxyIdx2 proxyIdx1

class SwapTerms_F product (idx1 :: Nat) (idx2 :: Nat) where
    swapTerms_ :: Index idx1 -> Index idx2 -> F Total Bijection product (SwapTerms_ product idx1 idx2)

instance {-# OVERLAPS #-}
    (
    ) => SwapTerms_F (p :*: q :*: r) 1 2
  where
    swapTerms_ _ _ = F fto ffrom
      where
        fto :: Total (p :*: q :*: r) (q :*: p :*: r)
        fto = arr (\(Product (p, Product (q, r))) -> Product (q, Product (p, r)))
        ffrom :: Bijection (q :*: p :*: r) (p :*: q :*: r)
        ffrom = arr (\(Product (q, (Product (p, r)))) -> Product (p, Product (q, r)))

instance {-# OVERLAPS #-}
    ( SwapTerms_ (p :*: q) 1 2 ~ (q :*: p)
    ) => SwapTerms_F (p :*: q) 1 2
  where
    swapTerms_ _ _ = F fto ffrom
      where
        fto :: Total (p :*: q) (q :*: p)
        fto = arr (\(Product (p, q)) -> Product (q, p))
        ffrom :: Bijection (q :*: p) (p :*: q)
        ffrom = arr (\(Product (q, p)) -> Product (p, q))

instance {-# OVERLAPS #-}
    (   (SwapTerms_ (p :*: q) 1 idx2)
      ~ ((Sub (p :*: q) idx2) :*: (ReplaceTerm p q (idx2 - 1)))

    -- The idx2 - 1 th component of ReplaceTerm p q (idx2 - 1) is p. That's
    -- obvious.
    ,   (Sub (ReplaceTerm p q (idx2 - 1)) (idx2 - 1))
      ~ p

    -- If you put p into q at place idx2 - 1, and then you put q into that
    -- at place idx2 - 1, you get the original q.
    ,   (ReplaceTerm (Sub (p :*: q) idx2) (ReplaceTerm p q (idx2 - 1)) (idx2 - 1))
      ~ q

    , Project (p :*: q) idx2
    , ReplaceTermF p q (idx2 - 1)
    , Project (ReplaceTerm p q (idx2 - 1)) (idx2 - 1)
    , ReplaceTermF (Sub (p :*: q) idx2) (ReplaceTerm p q (idx2 - 1)) (idx2 - 1)
    ) => SwapTerms_F (p :*: q) 1 idx2
  where
    swapTerms_ _ _ = F fto ffrom
      where
        fto :: Total (p :*: q) (SwapTerms_ (p :*: q) 1 idx2)
        fto = arr $ \(Product (a, b)) -> Product (
                          getComponent (project (Index :: Index idx2) (Product (a, b)))
                        , replaceTerm a b (Index :: Index (idx2 - 1))
                        )
        ffrom :: Bijection (SwapTerms_ (p :*: q) 1 idx2) (p :*: q)
        ffrom = arr $ \(Product (a, b)) -> Product (
                          -- b = replaceTerm p q (Index :: Index (idx2 - 1))
                          -- so we can get p just by projecting onto idx2 - 1.
                            getComponent (project (Index :: Index (idx2 - 1)) b)
                          -- a = getComponent (project (Index :: Index idx2) (p :*: q))
                          -- so how do we get q? Just put a into b at idx2 - 1.
                          , replaceTerm a b (Index :: Index (idx2 - 1))
                          )

instance {-# OVERLAPS #-}
    (   (SwapTerms_ (p :*: q) idx1 idx2)
      ~ (p :*: SwapTerms_ q (idx1 - 1) (idx2 - 1))
    , SwapTerms_F q (idx1 - 1) (idx2 - 1)
    ) => SwapTerms_F (p :*: q) idx1 idx2
  where
    swapTerms_ _ _ = reassembleProduct id
                   . useBottomOfProduct (swapTerms_ (Index :: Index (idx1 - 1)) (Index :: Index (idx2 - 1)))
                   . disassembleProduct


class SwapSummandsF sum index1 index2 where
    swapSummands
        :: Index index1
        -> Index index2
        -> F Total Bijection sum (SwapSummands sum index1 index2)

instance
    ( SwapSummandsFDisambiguated (SwapSummandsFamilyClause sum index1 index2) sum index1 index2
    ) => SwapSummandsF sum index1 index2
  where
    swapSummands = swapSummandsDisambiguated (Proxy :: Proxy (SwapSummandsFamilyClause sum index1 index2))

class  SwapSummandsFDisambiguated clauseNumber sum index1 index2 where
    swapSummandsDisambiguated
        :: Proxy clauseNumber
        -> Index index1
        -> Index index2
        -> F Total Bijection sum (SwapSummands sum index1 index2)

instance {-# OVERLAPS #-} SwapSummandsFDisambiguated 1 sum n n where
    swapSummandsDisambiguated _ _ _ = id

instance {-# OVERLAPS #-}
    ( SwapSummandsNormalizeF (a :+: b :+: c) index1 index2 (CmpNat index1 index2)
    ,   SwapSummands (a :+: b :+: c) index1 index2
      ~ SwapSummandsNormalize (a :+: b :+: c) index1 index2 (CmpNat index1 index2)
    ) => SwapSummandsFDisambiguated 2 (a :+: b :+: c) index1 index2
  where
    swapSummandsDisambiguated _ index1 index2 =
        swapSummandsNormalize index1 index2 (Proxy :: Proxy (CmpNat index1 index2))

instance {-# OVERLAPS #-}
    ( SwapSummands (a :+: b) 1 2 ~ (b :+: a)
    ) => SwapSummandsFDisambiguated 3 (a :+: b) 1 2
  where
    swapSummandsDisambiguated _ _ _ = F fto ffrom
      where
        fto = arr $ \(Sum sum) -> case sum of
                        Left l -> Sum (Right l)
                        Right r -> Sum (Left r)
        ffrom = arr $ \(Sum sum) -> case sum of
                          Left l -> Sum (Right l)
                          Right r -> Sum (Left r)

instance {-# OVERLAPS #-}
    ( SwapSummands (a :+: b) 2 1 ~ (b :+: a)
    ) => SwapSummandsFDisambiguated 4 (a :+: b) 2 1
  where
    swapSummandsDisambiguated _ _ _ = F fto ffrom
      where
        fto = arr $ \(Sum sum) -> case sum of
                        Left l -> Sum (Right l)
                        Right r -> Sum (Left r)
        ffrom = arr $ \(Sum sum) -> case sum of
                          Left l -> Sum (Right l)
                          Right r -> Sum (Left r)

class SwapSummandsNormalizeF sum index1 index2 order where
    swapSummandsNormalize
        :: Index index1
        -> Index index2
        -> Proxy order
        -> F Total Bijection sum (SwapSummandsNormalize sum index1 index2 order)

instance {-# OVERLAPS #-}
    ( SwapSummands_F sum index1 index2
    ) => SwapSummandsNormalizeF sum index1 index2 'LT
  where
    swapSummandsNormalize index1 index2 _ = swapSummands_ index1 index2

instance {-# OVERLAPS #-}
    ( SwapSummands_F sum index2 index1
    ) => SwapSummandsNormalizeF sum index1 index2 'GT
  where
    swapSummandsNormalize index1 index2 _ = swapSummands_ index2 index1

class SwapSummands_F sum index1 index2 where
    swapSummands_
        :: Index index1
        -> Index index2
        -> F Total Bijection sum (SwapSummands_ sum index1 index2)

instance {-# OVERLAPS #-}
    ( SwapSummands_ (p :+: q) 1 2 ~ (q :+: p)
    ) => SwapSummands_F (p :+: q) 1 2
  where
    swapSummands_ _ _ = F fto ffrom
      where
        fto = arr $ \(Sum sum) -> case sum of
                        Left p -> Sum (Right p)
                        Right q -> Sum (Left q)
        ffrom = arr $ \(Sum sum) -> case sum of
                          Left p -> Sum (Right p)
                          Right q -> Sum (Left q)

instance {-# OVERLAPS #-}
    (
    ) => SwapSummands_F (p :+: q :+: r) 1 2
  where
    swapSummands_ _ _ = F fto fto
      where
        fto = arr $ \(Sum sum) -> case sum of
                        Left p -> Sum (Right (Sum (Left p)))
                        Right (Sum (Left q)) -> Sum (Left q)
                        Right (Sum (Right r)) -> Sum (Right (Sum (Right r)))

-- Now, can we use SumDecompose to help implement swapping?
-- We decompose the @q@ at index2 - 1 and if it's left, we inject it at place
-- 1, else we have the remaining sum without index2 - 1 so we need to expand
-- that to include a place for @p@ where @q@ formerly was.
-- Do we have the tools to do that? That requires a class to mirror the
-- family IntroduceSummand.
-- Ok, so do that...

instance {-# OVERLAPS #-}
    ( SumDecompose q (index2 - 1)
    -- Obviously true, since SwapSummands_ (p :+: q) 1 index2 puts q at
    -- index 1.
    , Inject 1 (SummandAt q (index2 - 1)) (SwapSummands_ (p :+: q) 1 index2)
    -- Obviously true, since SummandAt q (index2 - 1) is in q.
    , Inject index2 (SummandAt q (index2 - 1)) (p :+: q)
    , SumRecompose p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1)
    , SumDecompose (IntroduceSummand p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1))
                   (index2 - 1)
    -- Obviously true: SwapSummands_ (p :+: q) 1 index2 puts
    -- SummandAt q (index2 - 1) at the front, and removes it from the same
    -- index, then introduces p at that same index.
    ,   (SwapSummands_ (p :+: q) 1 index2)
      ~ ((SummandAt q (index2 - 1)) :+: (IntroduceSummand p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1)))
    , Inject index2 p (SwapSummands_ (p :+: q) 1 index2)

    -- Obviously true: if we introduce p at index2 - 1, then p is the summand
    -- at index2 - 1
    ,   p
      ~ SummandAt (IntroduceSummand p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1)) (index2 - 1)

    -- Follow what happens to q:
    --
    --   1. Remove the thing at index2 - 1.
    --   2. Introduce p at index2 - 1.
    --   3. Remove the thing at index2 - 1.
    --   4. Introduce the index2'th thing from (p :+: q) at index2 - 1.
    --
    -- Result? The same thing you started with: q.
    ,   q
      ~ IntroduceSummand (SummandAt (p :+: q) index2)
                         (SumWithoutSummandAt (IntroduceSummand p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1))
                                              (index2 - 1))
                         (index2 - 1)

    , SumRecompose (SummandAt (p :+: q) index2)
                   (SumWithoutSummandAt (IntroduceSummand p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1))
                                        (index2 - 1))
                   (index2 - 1)

    ) => SwapSummands_F (p :+: q) 1 index2
  where
    swapSummands_ _ _ = F fto ffrom
      where

        fto :: Total (p :+: q) (SwapSummands_ (p :+: q) 1 index2)
        fto = arr $ \(Sum sum) -> case sum of
                        Left p -> inject (Index :: Index index2) p
                        Right q -> case sumDecompose q (Index :: Index (index2 - 1)) :: Either (SummandAt q (index2 - 1)) (SumWithoutSummandAt q (index2 - 1)) of
                                       Left q' -> inject (Index :: Index 1) q'
                                       Right rest -> Sum (Right (sumRecompose (Proxy :: Proxy p) rest (Index :: Index (index2 - 1))))

        ffrom :: Bijection (SwapSummands_ (p :+: q) 1 index2) (p :+: q)
        ffrom = arr $ \(Sum sum) -> case sum of
                          -- We know that
                          --   l :: (SummandAt q (index2 - 1))
                          -- all we've got to do is inject it at index2 into
                          --   p :+: q
                          -- which, by assumption, we can do.
                          -- If we've done anything right, this assumption
                          -- should always be satisfied.
                          Left l -> inject (Index :: Index index2) l
                          -- We know that rest is a sum containg p at index2 - 1.
                          -- Let's decompose it to see whether it's p.
                          Right rest -> case sumDecompose rest (Index :: Index (index2 - 1)) of
                                            Left p -> Sum (Left p)
                                            -- It's not p, so we just need to
                                            -- recompose the sum with
                                            -- SummandAt (p :+: q) index2 in
                                            -- place of p.
                                            Right rest' -> Sum (Right (sumRecompose (Proxy :: Proxy (SummandAt (p :+: q) index2)) rest' (Index :: Index (index2 - 1))))

instance {-# OVERLAPS #-}
    (   SwapSummands_ (p :+: q) index1 index2
      ~ (p :+: (SwapSummands_ q (index1 - 1) (index2 - 1)))
    , SwapSummands_F q (index1 - 1) (index2 - 1)
    ) => SwapSummands_F (p :+: q) index1 index2
  where
    swapSummands_ _ _ = reassembleSum id
                      . useBottomOfSum (swapSummands_ (Index :: Index (index1 - 1)) (Index :: Index (index2 - 1)))
                      . disassembleSum

-- | Given a product of Fs, get all of the fs, in order.
type family ProductTos (ps :: *) :: [* -> * -> *] where
    ProductTos ((F f g s t) :*: rest) = f ': ProductTos rest
    ProductTos (F f g s t) = '[f]

type family ProductFroms (ps :: *) :: [* -> * -> *] where
    ProductFroms ((F f g s t) :*: rest) = g ': ProductFroms rest
    ProductFroms (F f g s t) = '[g]

class ProductF product s t | product -> s, product -> t where
    productF
        :: product
        -> F (GLBFold (ProductTos product))
             (GLBFold (ProductFroms product))
             s
             t

instance {-# OVERLAPS #-} ProductF (F f g s t) s t where
    productF = id

instance {-# OVERLAPS #-}
    ( Arrow f
    , Arrow g
    , Arrow (GLBFold (ProductTos rest))
    , Arrow (GLBFold (ProductFroms rest))
    -- These are here so we can do
    --   useBottomOfProduct recursive <.> disassemble
    , Composable Total (GLBFold (ProductTos rest))
    , Composable Bijection (GLBFold (ProductFroms rest))
    -- These are here so we can do
    --   reassemble <.> useBottomOfProduct recursive <.> disassemble
    , Composable f (GLBFold (ProductTos rest))
    , Composable g (GLBFold (ProductFroms rest))
    , ProductF rest srest trest
    ) => ProductF ((F f g s t) :*: rest) (s :*: srest) (t :*: trest)
  where
    productF (Product (a, b)) =
        let recursive :: F (GLBFold (ProductTos rest))
                           (GLBFold (ProductFroms rest))
                           srest
                           trest
            recursive = productF b
            disassemble :: F Total Bijection (s :*: srest) (s, srest)
            disassemble = disassembleProduct
            reassemble :: F f g (s, trest) (t :*: trest)
            reassemble = reassembleProduct a
        in  reassemble <.> useBottomOfProduct recursive <.> disassemble

-- | A product of F's can become an F on sums.
--   This is akin to pattern matching.
class SumF product s t | product -> s, product -> t where
    sumF
        :: product
        -> F (GLBFold (ProductTos product))
             (GLBFold (ProductFroms product))
             s
             t

instance {-# OVERLAPS #-} SumF (F f g s t) s t where
    sumF = id

instance {-# OVERLAPS #-}
    ( ArrowChoice f
    , ArrowChoice g
    , ArrowChoice (GLBFold (ProductTos rest))
    , ArrowChoice (GLBFold (ProductFroms rest))
    , Composable Total (GLBFold (ProductTos rest))
    , Composable Bijection (GLBFold (ProductFroms rest))
    , Composable f (GLBFold (ProductTos rest))
    , Composable g (GLBFold (ProductFroms rest))
    , SumF rest srest trest
    ) => SumF ((F f g s t) :*: rest) (s :+: srest) (t :+: trest)
  where
    -- Notice the symmetry to the definition of productF
    sumF (Product (a, b)) =
        let recursive :: F (GLBFold (ProductTos rest))
                           (GLBFold (ProductFroms rest))
                           srest
                           trest
            recursive = sumF b
            disassemble :: F Total Bijection (s :+: srest) (Either s srest)
            disassemble = disassembleSum
            reassemble :: F f g (Either s trest) (t :+: trest)
            reassemble = reassembleSum a
        in  reassemble <.> useBottomOfSum recursive <.> disassemble

-- | This is a bit like ProductF, but for a product of F's whose domain and
--   codomain are homogeneous: every term in the product is an endomorphism
--   and they're all the same type of endomorphism. In this case, we sequence
--   them all, obtaining an F from a singleton to a singleton.
class SequenceProduct product f g s | product -> f, product -> g, product -> s where
    sequenceProduct :: product -> F f g s s

instance {-# OVERLAPS #-} SequenceProduct (F f g s s) f g s where
    sequenceProduct = id

instance {-# OVERLAPS #-}
    ( Category f
    , Category g
    , SequenceProduct rest f g s
    ) => SequenceProduct ((F f g s s) :*: rest) f g s
  where
    sequenceProduct (Product (a, b)) = a . sequenceProduct b

-- | For any product of (), there is a total bijection to ():
--
--       F Total Bijection ( () x ... x () ) ()
--
class TotalBijectionOfUnitProduct product where
    totalBijectionOfUnitProduct :: F Total Bijection product ()

instance TotalBijectionOfUnitProduct () where
    totalBijectionOfUnitProduct = F id id

instance
    ( TotalBijectionOfUnitProduct rest
    ) => TotalBijectionOfUnitProduct (() :*: rest)
  where
    totalBijectionOfUnitProduct = totalBijectionOfUnitProduct . eliminateTerm one

-- | For any homogeneous sum, there is a total surjection onto the type
--   of the summands:
--
--       F Total Surjection ( s + ... + s ) s
--
class TotalSurjectionOfHomogeneousSum sum where
    totalSurjectionOfHomogeneousSum :: F Total Surjection sum (HomogeneousSumType sum)

instance {-# OVERLAPS #-}
    ( s ~ HomogeneousSumType s
    ) => TotalSurjectionOfHomogeneousSum s
  where
    totalSurjectionOfHomogeneousSum = F id id

instance {-# OVERLAPS #-}
    ( TotalSurjectionOfHomogeneousSum rest
    , HomogeneousSumImage (s :+: rest) (HomogeneousSumType (s :+: rest))
    , HomogeneousSumPreimage (s :+: rest) (HomogeneousSumType (s :+: rest))
    ) => TotalSurjectionOfHomogeneousSum (s :+: rest)
  where
    totalSurjectionOfHomogeneousSum = F fto ffrom
      where
        fto :: Total (s :+: rest) s
        fto = arr homogeneousSumImage
        ffrom :: Surjection s (s :+: rest)
        ffrom = Kleisli homogeneousSumPreimage

-- | This class and its instances give us, for any summand, a total injection
--   into any sum containing that summand at the given index.
class TotalInjectionOfSummand index sum where
    totalInjectionOfSummand
        :: Index index
        -> F Total Injection (SummandAt sum index) sum

instance {-# OVERLAPS #-}
    ( s ~ SummandAt s 1
    ) => TotalInjectionOfSummand 1 s
  where
    totalInjectionOfSummand _ = F returnA returnA

instance {-# OVERLAPS #-}
    (
    ) => TotalInjectionOfSummand 1 (s :+: rest)
  where
    totalInjectionOfSummand _ = F fto ffrom
      where
        fto :: Total s (s :+: rest)
        fto = arr $ \s -> Sum (Left s)
        ffrom :: Injection (s :+: rest) s
        ffrom = Kleisli $ \(Sum sum) -> case sum of
                              Left s -> Just s
                              Right _ -> Nothing

instance {-# OVERLAPS #-}
    ( SummandAt rest (n - 1) ~ SummandAt (s :+: rest) n
    , TotalInjectionOfSummand (n - 1) rest
    ) => TotalInjectionOfSummand n (s :+: rest)
  where
    totalInjectionOfSummand _ =
        let recursive :: F Total
                           Injection
                           (SummandAt rest (n - 1))
                           rest
            recursive = totalInjectionOfSummand (Index :: Index (n - 1))

            reassemble :: F Total
                            Injection
                            (rest)
                            (s :+: rest)
            reassemble = F fto ffrom
              where
                fto :: Total rest (s :+: rest)
                fto = arr $ Sum . Right
                ffrom :: Injection (s :+: rest) rest
                ffrom = Kleisli $ \(Sum sum) -> case sum of
                                      Left _ -> Nothing
                                      Right r -> Just r

        in  reassemble <.> recursive

type family HomogeneousSumType sum :: * where
    HomogeneousSumType (s :+: rest) = s
    HomogeneousSumType s = s

-- | Pick a value from a homogeneous sum.
class HomogeneousSumImage sum image where
    homogeneousSumImage :: sum -> image

instance {-# OVERLAPS #-} HomogeneousSumImage sum sum where
    homogeneousSumImage = id

instance {-# OVERLAPS #-}
    ( HomogeneousSumImage rest s
    ) => HomogeneousSumImage (s :+: rest) s
  where
    homogeneousSumImage (Sum sum) = case sum of
        Left x -> x
        Right rest -> homogeneousSumImage rest

-- | Give a value and we can produce the preimage of that value in a function
--   from a homogeneous sum of the same type as that value. For instance:
--   
--       sumPreimage "hello world" :: NonEmpty (String :+: String :+: String)
--
--   has three elements: "hello world" in any of the three components.
class HomogeneousSumPreimage sum image where
    homogeneousSumPreimage :: image -> NonEmpty sum

instance {-# OVERLAPS #-} HomogeneousSumPreimage sum sum where
    homogeneousSumPreimage = pure

instance {-# OVERLAPS #-}
    ( HomogeneousSumPreimage rest s
    ) => HomogeneousSumPreimage (s :+: rest) s
  where
    homogeneousSumPreimage x =
           pure (Sum (Left x))
        <> fmap (Sum . Right) (homogeneousSumPreimage x :: NonEmpty rest)

-- | By choosing a particular summand to use in the `to` direction, and
--   trying all summands in the `from` direction, we get at most a total
--   surjection from s t *through* any `F` on homogeneous sums of s and t.
--
--   Note that this *cannot* be expressed in terms of
--     totalInjectionOfSummand
--   and
--     totalSurjectionOfHomogeneousSum
--   as that would give us a Total Function. But here we are able to obtain
--   a Total Surjection. The crucial difference: totalInjectionOfSummand
--   just doesn't have enough information to give anything better than an
--   injection.
homogeneousSumIndexedSurjection
    :: forall index g h ssum tsum .
       ( Arrow g
       , Arrow h
       , WitnessGLB g Total
       , GLB g Total ~ GLB Total g
       , WitnessGLB h Surjection
       , WitnessGLB Surjection h
       , Arrow (GLB h Surjection)
       , GLB h Surjection ~ GLB Surjection h
       , TotalSurjectionOfHomogeneousSum tsum
       , TotalInjectionOfSummand index tsum
       -- Obivously true: tsum is homogeneous!
       , HomogeneousSumType tsum ~ SummandAt tsum index
       , Inject index (HomogeneousSumType ssum) ssum
       , HomogeneousSumImage ssum (HomogeneousSumType ssum)
       )
    => Index index
    -> F g h ssum tsum
    -> F (GLB Total g)
         (GLB Surjection h)
         (HomogeneousSumType ssum)
         (HomogeneousSumType tsum)
homogeneousSumIndexedSurjection index f =
    let totalSurjection :: F Total Surjection tsum (HomogeneousSumType tsum)
        totalSurjection = totalSurjectionOfHomogeneousSum
        totalInjection :: F Total Injection (HomogeneousSumType tsum) tsum
        totalInjection = totalInjectionOfSummand index

        fto :: (GLB Total g) (HomogeneousSumType ssum) (HomogeneousSumType tsum)
        fto = let injectIt :: HomogeneousSumType ssum -> ssum
                  injectIt = inject index
                  forward :: (GLB g Total) ssum tsum
                  forward = witnessGLB (Proxy :: Proxy Total) (to f)
                  collapse :: (GLB Total g) tsum (HomogeneousSumType tsum)
                  collapse = witnessGLB (Proxy :: Proxy g) (to totalSurjection)
              in  collapse . forward . arr injectIt

        ffrom :: (GLB Surjection h) (HomogeneousSumType tsum) (HomogeneousSumType ssum)
        ffrom = let uncollapse :: (GLB Surjection h) (HomogeneousSumType tsum) tsum
                    uncollapse = witnessGLB (Proxy :: Proxy h) (from totalSurjection)
                    backward :: (GLB h Surjection) tsum ssum
                    backward = witnessGLB (Proxy :: Proxy Surjection) (from f)
                    replaceIt :: ssum -> HomogeneousSumType ssum
                    replaceIt = homogeneousSumImage
                in  arr replaceIt . backward . uncollapse

    in  F fto ffrom

reassembleProduct
    :: forall f g s t any .
       ( Arrow f
       , Arrow g
       )
    => F f g s t
    -> F f g (s, any) (t :*: any)
reassembleProduct f = F fto ffrom
  where
    fto :: f (s, any) (t :*: any)
    fto = (arr Product)
        . first (to f)
    ffrom :: g (t :*: any) (s, any)
    ffrom = first (from f)
          . arr (\(Product (x, rest)) -> (x, rest))

useBottomOfProduct
    :: forall f g s t any .
       ( Arrow f
       , Arrow g
       )
    => F f g s t
    -> F f g (any, s) (any, t)
useBottomOfProduct f = F fto ffrom
  where
    fto :: f (any, s) (any, t)
    fto = second (to f)
    ffrom :: g (any, t) (any, s)
    ffrom = second (from f)

disassembleProduct
    :: forall f g s t any .
       ( Arrow f
       , Arrow g
       )
    => F f g (s :*: t) (s, t)
disassembleProduct = F (arr (\(Product (a, b)) -> (a, b))) (arr Product)

-- | Notice the symmetry to reassembleProduct.
reassembleSum
    :: forall f g s t any .
       ( ArrowChoice f
       , ArrowChoice g
       )
    => F f g s t
    -> F f g (Either s any) (t :+: any)
reassembleSum f = F fto ffrom
  where
    fto :: f (Either s any) (t :+: any)
    fto = (arr Sum)
        . left (to f)
    ffrom :: g (t :+: any) (Either s any)
    ffrom = left (from f)
          . arr (\(Sum sum) -> sum)

-- | Notice the symmetry to useBottomOfProduct.
useBottomOfSum
    :: forall f g s t any .
       ( ArrowChoice f
       , ArrowChoice g
       )
    => F f g s t
    -> F f g (Either any s) (Either any t)
useBottomOfSum f = F fto ffrom
  where
    fto :: f (Either any s) (Either any t)
    fto = right (to f)
    ffrom :: g (Either any t) (Either any s)
    ffrom = right (from f)

-- | Notice the symmetry to disassembleProduct.
disassembleSum
    :: forall f g s t any .
       ( Arrow f
       , Arrow g
       )
    => F f g (s :+: t) (Either s t)
disassembleSum = F (arr (\(Sum sum) -> sum)) (arr (\sum -> Sum sum))

-- | Like @first@ for arrows.
thru :: (Arrow f, Arrow g) => F f g s t -> F f g (s, c) (t, c)
thru f = F (first (to f)) (first (from f))

-- | Pass over an F by supplying a fixed input and output.
pass :: (Arrow f, Arrow g) => s -> t -> F f g s t -> F f g c c
pass x y f = known x f >>> forget y f

-- | Give an input value for one F, thereby producing a new F where the input
--   is free.
known :: (Arrow f, Arrow g) => s -> F f g s t -> F f g c (t, c)
known x f = F fto ffrom
  where
    fto = (arr (\c -> (x, c))) >>> (first (to f))
    ffrom = (first (from f)) >>> (arr (\(x, c) -> c))
    -- fto . ffrom = (arr (\(x, c) -> c))
    --             . (first (from f))
    --             . (first (to f))
    --             . (arr (\c -> (x, c)))
    --
    --             = (arr (\(x, c) -> c))
    --             . (first (from f . to f))
    --             . (arr (\c -> (x, c)))
    --
    --             = (arr (\(x, c) -> c))
    --             . (first returnA)
    --             . (arr (\c -> (x, c)))
    --
    --             = (arr (\(x, c) -> c))
    --             . (arr (\(x, c) -> (x, c)))
    --             . (arr (\c -> (x, c)))
    --
    --             = (arr (\(x, c) -> c))
    --             . (arr (\c -> (x, c))
    --             
    --             = arr ((\(x, c) -> c) . (\c -> (x, c)))
    --
    --             = arr (\c -> c)
    --
    --             = arr id
    --
    --             = returnA

forget :: (Arrow f, Arrow g) => t -> F f g s t -> F f g (t, c) c
forget y f = F fto ffrom
  where
    fto = arr (\(x, y) -> y)
    ffrom = arr (\z -> (y, z))
    -- fto . ffrom = (arr (\(x, y) -> y))
    --             . (arr (\z -> (y, z)))
    --
    --             = arr ((\(x, y) -> y) . (\z -> (y, z)))
    --
    --             = arr (\z -> z)
    --
    --             = arr id
    --
    --             = returnA

-- TBD does this really preserve the *jection properties? Must obviously
-- use the traversable and arrowapply laws to prove it.
throughTraversable
    :: forall f g m a b .
       ( ArrowApply f
       , ArrowApply g
       , Traversable m
       )
    => F f g a b
    -> F f g (m a) (m b)
throughTraversable f = F (fto (to f)) (ffrom (from f))
  where

    fto :: f a b -> f (m a) (m b)
    fto = arrowFmap >>> arrowSequence >>> ((.) (arr runArrowMonad)) >>> arrowJoin

    ffrom :: g b a -> g (m b) (m a)
    ffrom = arrowFmap >>> arrowSequence >>> ((.) (arr runArrowMonad)) >>> arrowJoin

    arrowFmap
        :: forall f m a b .
           ( Arrow f
           , Functor m
           )
        => f a b
        -> f (m a) (m (ArrowMonad f b))
    arrowFmap f = arr (fmap (\x -> ArrowMonad (arr (const x) >>> f)))

    arrowSequence
        :: forall f m a b .
           ( Arrow f
           , Traversable m
           )
        => f (m a) (m (ArrowMonad f b))
        -> f (m a) (ArrowMonad f (m b))
    arrowSequence = (.) (arr sequenceA)

    arrowJoin
        :: forall f m a b .
           ArrowApply f
        => f (m a) (f () (m b))
        -> f (m a) (m b)
    arrowJoin x = proc m -> do
        y <- x -< m
        z <- app -< (y, ())
        returnA -< z

    runArrowMonad :: forall a b . ArrowMonad a b -> a () b
    runArrowMonad (ArrowMonad x) = x
