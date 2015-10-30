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
    , pair
    , pass
    , known
    , forget
    , throughTraversable
    , eliminateTerm
    , introduceTerm
    , swapTerms
    , TotalBijectionOfUnitProduct
    , totalBijectionOfUnitProduct
    , TotalSurjectionOfHomogeneousSum
    , totalSurjectionOfHomogeneousSum
    , HomogeneousSumImage
    , homogeneousSumImage
    , HomogeneousSumPreimage
    , homogeneousSumPreimage

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
    swapTerms :: Index idx1 -> Index idx2 -> F Total Bijection product (SwapTerms product idx1 idx2)

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


-- | Given a product of Fs, get all of the fs, in order.
type family ProductTos (ps :: *) :: [* -> * -> *] where
    ProductTos ((F f g s t) :*: rest) = f ': ProductTos rest
    ProductTos (F f g s t) = '[f]

type family ProductFroms (ps :: *) :: [* -> * -> *] where
    ProductFroms ((F f g s t) :*: rest) = g ': ProductFroms rest
    ProductFroms (F f g s t) = '[g]

-- | A product of F's can become an F on products.
class ProductF product f g s t | product -> f, product -> g, product -> s, product -> t where
    productF :: product -> F f g s t

instance {-# OVERLAPS #-} ProductF (F f g product t) f g product t where
    productF = id

instance {-# OVERLAPS #-}
    ( Arrow f
    , Arrow g
    , ProductF frest f g rest trest
    ) => ProductF ((F f g s t) :*: frest) f g (s :*: rest) (t :*: trest)
  where
    productF (Product (a, b)) = reassembleProduct a
                              . useBottomOfProduct (productF b)
                              . disassembleProduct

-- | A product of F's can become an F on sums.
--   This is akin to pattern matching.
class SumF product f g s t | product -> f, product -> g, product -> s, product -> t where
    sumF :: product -> F f g s t

instance {-# OVERLAPS #-} SumF (F f g summand t) f g summand t where
    sumF = id

instance {-# OVERLAPS #-}
    ( ArrowChoice f
    , ArrowChoice g
    , SumF frest f g srest trest
    ) => SumF ((F f g s t) :*: frest) f g (s :+: srest) (t :+: trest)
  where
    -- Notice the symmetry to the definition of productF
    sumF (Product (a, b)) = reassembleSum a
                          . useBottomOfSum (sumF b)
                          . disassembleSum


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
pair :: (Arrow f, Arrow g) => F f g s t -> F f g (s, c) (t, c)
pair f = F (first (to f)) (first (from f))

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
