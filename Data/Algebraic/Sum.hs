{-|
Module      : Data.Algebraic.Sum
Description : Algebraic datatype sums.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Algebraic.Sum (

      Sum(..)
    , (:+:)
    , SummandAt
    , SumWithoutSummandAt
    , SumDecompose
    , sumDecompose
    , SumRecompose
    , sumRecompose
    , Inject
    , inject
    , EliminateSummand
    , IntroduceSummand
    , SwapSummands
    , SwapSummandsNormalize
    , SwapSummands_
    , SwapSummandsF
    , swapSummands
    , ReplaceSummand
    , ReplaceSummandF
    , replaceSummand
    , FoldSum
    , foldSum
    , ApplyFunctionToHomogeneousSum
    , applyFunctionToHomogeneousSum

    ) where

import GHC.TypeLits
import Data.Proxy
import Data.Void
import Data.Algebraic.Index

newtype Sum a b = Sum (Either a b)

type a :+: b = Sum a b
infixr 8 :+:

-- | Very useful for avoiding class overlap.
type family SumSize (t :: *) :: Nat where
    SumSize (a :+: b) = 1 + SumSize b
    SumSize a = 1

instance {-# OVERLAPS #-}
    ( ShowSumTagged 1 (Sum a b)
    ) => Show (Sum a b)
  where
    show = showSumTagged (Index :: Index 1)

class ShowSumTagged (index :: Nat) sum where
    showSumTagged :: Index index -> sum -> String

-- For singleton sums.
instance {-# OVERLAPS #-}
    ( Show sum
    , Show (Index n)
    ) => ShowSumTagged n sum
  where
    showSumTagged _ x = concat [
           "Summand "
        , show (Index :: Index n)
        , " : "
        , show x
        ]

instance {-# OVERLAPS #-}
    ( Show sum
    , ShowSumTagged (n + 1) rest
    , Show (Index n)
    ) => ShowSumTagged n (sum :+: rest)
  where
    showSumTagged _ (Sum x) = case x of
        Left x' -> concat [
              "Summand "
            , show (Index :: Index n)
            , " : "
            , show x'
            ]
        Right rest -> showSumTagged (Index :: Index (n + 1)) rest

type family SummandAt sum (index :: Nat) where
    SummandAt (summand :+: rest) 1 = summand
    SummandAt summand 1 = summand
    SummandAt (summand :+: rest) n = SummandAt rest (n - 1)

type family SumWithoutSummandAt sum (index :: Nat) where
    SumWithoutSummandAt (summand :+: rest) 1 = rest
    SumWithoutSummandAt (summand :+: p :+: rest) 2 = summand :+: rest
    SumWithoutSummandAt (summand :+: rest) 2 = summand
    SumWithoutSummandAt (summand :+: rest) n = summand :+: (SumWithoutSummandAt rest (n - 1))

-- | Decompose a sum at an index. If that index is where the value is, you get
--   that value; otherwise, you get a sum with that place removed.
--
--     Index index -> sum -> Either (SummandAt sum index) (SumWithoutSummandAt sum index)
--
class SumDecompose sum index where
    sumDecompose
        :: sum
        -> Index index
        -> Either (SummandAt sum index) (SumWithoutSummandAt sum index)

instance {-# OVERLAPS #-}
    (
    ) => SumDecompose (summand :+: rest) 1
  where
    sumDecompose (Sum sum) _ = case sum of
        Left x -> Left x
        Right rest -> Right rest

instance {-# OVERLAPS #-}
    (
    ) => SumDecompose (summand :+: p :+: rest) 2
  where
    sumDecompose (Sum sum) _ = case sum of
        Left l -> Right (inject one l :: (summand :+: rest))
        Right (Sum (Left p)) -> Left p
        Right (Sum (Right rest)) -> Right (Sum (Right rest))

instance {-# OVERLAPS #-}
    ( -- With these constraints we say, in a round-about way, that
      -- rest is not a sum.
      summand ~ SumWithoutSummandAt (summand :+: rest) 2
    , rest ~ SummandAt rest 1
    ) => SumDecompose (summand :+: rest) 2
  where
    sumDecompose (Sum sum) _ = case sum of
        Left l -> Right l
        Right r -> Left r

instance {-# OVERLAPS #-}
    ( SummandAt (summand :+: rest) n ~ SummandAt (rest) (n - 1)
    , SumWithoutSummandAt (summand :+: rest) n ~ (summand :+: SumWithoutSummandAt (rest) (n - 1))
    , SumDecompose rest (n - 1)
    ) => SumDecompose (summand :+: rest) n
  where
    sumDecompose (Sum sum) _ = case sum of
        Left x -> Right (inject one x :: summand :+: SumWithoutSummandAt rest (n - 1))
        Right rest -> case sumDecompose rest (Index :: Index (n - 1)) of
            Left found -> Left found
            Right notFound -> Right (Sum (Right notFound))

class SumRecompose s sum index where
    sumRecompose :: Proxy s -> sum -> Index index -> IntroduceSummand s sum index

instance {-# OVERLAPS #-}
    (
    ) => SumRecompose r (s :+: rest) 1
  where
    sumRecompose _ sum _ = Sum (Right sum)

instance {-# OVERLAPS #-}
    (
    ) => SumRecompose r (s :+: rest) 2
  where
    sumRecompose _ (Sum sum) _ = case sum of
        Left l -> Sum (Left l)
        Right r -> Sum (Right (Sum (Right r)))

instance {-# OVERLAPS #-}
    ( IntroduceSummand r (s :+: rest) n ~ (s :+: IntroduceSummand r rest (n - 1))
    , SumRecompose r rest (n - 1)
    ) => SumRecompose r (s :+: rest) n
  where
    sumRecompose proxyR (Sum sum) _ = case sum of
        Left s -> Sum (Left s)
        Right rest -> Sum (Right (sumRecompose proxyR rest (Index :: Index (n - 1))))

instance {-# OVERLAPS #-}
    ( IntroduceSummand r p 2 ~ (p :+: r)
    ) => SumRecompose r p 2
  where
    sumRecompose _ p _ = Sum (Left p)

instance {-# OVERLAPS #-}
    ( IntroduceSummand r p 1 ~ (r :+: p)
    ) => SumRecompose r p 1
  where
    sumRecompose _ p _ = Sum (Right p)

class Inject index summand sum where
    inject :: Index index -> summand -> sum

instance {-# OVERLAPS #-} Inject 1 summand summand where
    inject _ = id

instance {-# OVERLAPS #-} Inject 1 summand (summand :+: rest) where
    inject _ = Sum . Left

instance {-# OVERLAPS #-}
    ( Inject (n - 1) summand rest
    ) => Inject n summand (summand' :+: rest)
  where
    inject _ = Sum . Right . inject (Index :: Index (n - 1))

type family EliminateSummand sum (index :: Nat) where
    EliminateSummand (p :+: rest) 1 = rest
    EliminateSummand (p :+: q :+: rest) n = p :+: EliminateSummand (q :+: rest) (n - 1)
    EliminateSummand (p :+: q) 2 = p
    EliminateSummand (p :+: rest) n = p :+: EliminateSummand rest (n - 1)
    EliminateSummand p 1 = Void

type family IntroduceSummand r sum (index :: Nat) where
    IntroduceSummand r (p :+: rest) 1 = r :+: p :+: rest
    IntroduceSummand r (p :+: rest) 2 = p :+: r :+: rest
    IntroduceSummand r (p :+: rest) n = p :+: IntroduceSummand r rest (n - 1)
    IntroduceSummand r p 2 = p :+: r
    IntroduceSummand r p 1 = r :+: p

type family SwapSummands sum (idx1 :: Nat) (idx2 :: Nat) where
    SwapSummands p n n = p
    SwapSummands (a :+: b :+: c) idx1 idx2 = SwapSummandsNormalize (a :+: b :+: c) idx1 idx2 (CmpNat idx1 idx2)
    SwapSummands (a :+: b) 1 2 = b :+: a
    SwapSummands (a :+: b) 2 1 = b :+: a

-- | Useful for avoiding overlap.
type family SwapSummandsFamilyClause sum index1 index2 where
    SwapSummandsFamilyClause p n n = 1
    SwapSummandsFamilyClause (a :+: b :+: c) idx1 idx2 = 2
    SwapSummandsFamilyClause (a :+: b) 1 2 = 3
    SwapSummandsFamilyClause (a :+: b) 2 1 = 4

type family SwapSummandsNormalize sum (idx1 :: Nat) (idx2 :: Nat) (order :: Ordering) where
    SwapSummandsNormalize p idx1 idx2 'LT = SwapSummands_ p idx1 idx2
    SwapSummandsNormalize p idx1 idx2 'GT = SwapSummands_ p idx2 idx1

-- We assume idx1 < idx2
type family SwapSummands_ sum (idx1 :: Nat) (idx2 :: Nat) where
    SwapSummands_ (p :+: q :+: r) 1 2 = q :+: p :+: r
    SwapSummands_ (p :+: q) 1 2 = q :+: p
    SwapSummands_ (p :+: q) 1 idx2 = (SummandAt (p :+: q) idx2) :+: (ReplaceSummand p q (idx2 - 1))
    SwapSummands_ (p :+: q) idx1 idx2 = p :+: (SwapSummands_ q (idx1 - 1) (idx2 - 1))

class SwapSummandsF sum index1 index2 where
    swapSummands
        :: sum
        -> Index index1
        -> Index index2
        -> SwapSummands sum index1 index2

instance
    ( SwapSummandsFDisambiguated (SwapSummandsFamilyClause sum index1 index2) sum index1 index2
    ) => SwapSummandsF sum index1 index2
  where
    swapSummands = swapSummandsDisambiguated (Proxy :: Proxy (SwapSummandsFamilyClause sum index1 index2))

class  SwapSummandsFDisambiguated clauseNumber sum index1 index2 where
    swapSummandsDisambiguated
        :: Proxy clauseNumber
        -> sum
        -> Index index1
        -> Index index2
        -> SwapSummands sum index1 index2

instance {-# OVERLAPS #-} SwapSummandsFDisambiguated 1 sum n n where
    swapSummandsDisambiguated _ x _ _ = x

-- This overlaps with the next one. How to avoid?
instance {-# OVERLAPS #-}
    ( SwapSummandsNormalizeF (a :+: b :+: c) index1 index2 (CmpNat index1 index2)
    ,   SwapSummands (a :+: b :+: c) index1 index2
      ~ SwapSummandsNormalize (a :+: b :+: c) index1 index2 (CmpNat index1 index2)
    ) => SwapSummandsFDisambiguated 2 (a :+: b :+: c) index1 index2
  where
    swapSummandsDisambiguated _ sum index1 index2 =
        swapSummandsNormalize sum index1 index2 (Proxy :: Proxy (CmpNat index1 index2))

instance {-# OVERLAPS #-}
    ( SwapSummands (a :+: b) 1 2 ~ (b :+: a)
    ) => SwapSummandsFDisambiguated 3 (a :+: b) 1 2
  where
    swapSummandsDisambiguated _ (Sum sum) _ _ = case sum of
        Left l -> Sum (Right l)
        Right r -> Sum (Left r)

instance {-# OVERLAPS #-}
    ( SwapSummands (a :+: b) 2 1 ~ (b :+: a)
    ) => SwapSummandsFDisambiguated 4 (a :+: b) 2 1
  where
    swapSummandsDisambiguated _ (Sum sum) _ _ = case sum of
        Left l -> Sum (Right l)
        Right r -> Sum (Left r)

class SwapSummandsNormalizeF sum index1 index2 order where
    swapSummandsNormalize
        :: sum
        -> Index index1
        -> Index index2
        -> Proxy order
        -> SwapSummandsNormalize sum index1 index2 order

instance {-# OVERLAPS #-}
    ( SwapSummands_F sum index1 index2
    ) => SwapSummandsNormalizeF sum index1 index2 'LT
  where
    swapSummandsNormalize sum index1 index2 _ = swapSummands_ sum index1 index2

instance {-# OVERLAPS #-}
    ( SwapSummands_F sum index2 index1
    ) => SwapSummandsNormalizeF sum index1 index2 'GT
  where
    swapSummandsNormalize sum index1 index2 _ = swapSummands_ sum index2 index1

class SwapSummands_F sum index1 index2 where
    swapSummands_
        :: sum
        -> Index index1
        -> Index index2
        -> SwapSummands_ sum index1 index2

instance {-# OVERLAPS #-}
    ( SwapSummands_ (p :+: q) 1 2 ~ (q :+: p)
    ) => SwapSummands_F (p :+: q) 1 2
  where
    swapSummands_ (Sum sum) _ _ = case sum of
        Left p -> Sum (Right p)
        Right q -> Sum (Left q)

instance {-# OVERLAPS #-}
    (
    ) => SwapSummands_F (p :+: q :+: r) 1 2
  where
    swapSummands_ (Sum sum) _ _ = case sum of
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
    , SumRecompose p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1)
    -- Obviously true: SwapSummands_ (p :+: q) 1 index2 puts
    -- SummandAt q (index2 - 1) at the front, and removes it from the same
    -- index, then introduces p at that same index.
    ,   (SwapSummands_ (p :+: q) 1 index2)
      ~ ((SummandAt q (index2 - 1)) :+: (IntroduceSummand p (SumWithoutSummandAt q (index2 - 1)) (index2 - 1)))
    , Inject index2 p (SwapSummands_ (p :+: q) 1 index2)
    ) => SwapSummands_F (p :+: q) 1 index2
  where
    swapSummands_ (Sum sum) _ _ = case sum of
        -- If we have Left then we can just inject it into the desired output.
        Left p -> inject (Index :: Index index2) p
        -- If we have Right then what? We have to somehow turn q into
        --   (SummandAt (p :+: q) index2) :+: (ReplaceSummand p q (index2 - 1))
        -- but it's not clear how to do that.
        Right q -> case sumDecompose q (Index :: Index (index2 - 1)) :: Either (SummandAt q (index2 - 1)) (SumWithoutSummandAt q (index2 - 1)) of
            Left q' -> inject (Index :: Index 1) q'
            Right rest -> Sum (Right (sumRecompose (Proxy :: Proxy p) rest (Index :: Index (index2 - 1))))

instance {-# OVERLAPS #-}
    ( SwapSummands_F q (index1 - 1) (index2 - 1)
    ,   SwapSummands_ (p :+: q) index1 index2
      ~ (p :+: (SwapSummands_ q (index1 - 1) (index2 - 1)))
    ) => SwapSummands_F (p :+: q) index1 index2
  where
    swapSummands_ (Sum sum) _ _ = case sum of
        Left p -> Sum (Left p)
        Right q -> Sum (Right (swapSummands_ q (Index :: Index (index1 - 1)) (Index :: Index (index2 - 1))))

type family ReplaceSummand p sum (idx2 :: Nat) where
    ReplaceSummand p (q :+: rest) 1 = (p :+: rest)
    ReplaceSummand p q 1 = p
    ReplaceSummand p (q :+: rest) idx2 = q :+: (ReplaceSummand p rest (idx2 - 1))

-- Isn't this just inject?
class ReplaceSummandF p q (idx :: Nat) where
    replaceSummand :: p -> q -> Index idx -> ReplaceSummand p q idx

instance {-# OVERLAPS #-}
    (
    ) => ReplaceSummandF p (q :+: rest) 1
  where
    replaceSummand p (Sum x) _ = case x of
        Left q -> Sum (Left p)
        Right rest -> Sum (Right rest)

instance {-# OVERLAPS #-}
    ( ReplaceSummand p q 1 ~ p
    ) => ReplaceSummandF p q 1
  where 
    replaceSummand p _ _ = p

instance {-# OVERLAPS #-}
    ( ReplaceSummand p (q :+: rest) idx2 ~ (q :+: (ReplaceSummand p rest (idx2 - 1)))
    , ReplaceSummandF p rest (idx2 - 1)
    ) => ReplaceSummandF p (q :+: rest) idx2
  where
    replaceSummand p (Sum x) _ = case x of
        Left q -> Sum (Left q)
        Right rest -> Sum (Right (replaceSummand p rest (Index :: Index (idx2 - 1))))

-- | This is an analogue of FoldProduct: we can select a value from a
--   homogeneous sum.
class FoldSum sum t where
    foldSum :: sum -> t

instance {-# OVERLAPS #-} FoldSum t t where
    foldSum = id

instance {-# OVERLAPS #-}
    ( FoldSum rest t
    ) => FoldSum (t :+: rest) t
  where
    foldSum (Sum sum) = case sum of
        Left x -> x
        Right rest -> foldSum rest

{-
 - We need a way to take a homogeneous sum and place every component into
 - a tuple. Here's one way to do it...
-}

class ApplyFunctionToHomogeneousSum sum sum' f where
    applyFunctionToHomogeneousSum :: f -> sum -> sum'

instance {-# OVERLAPS #-} ApplyFunctionToHomogeneousSum s t (s -> t) where
    applyFunctionToHomogeneousSum f = f

instance {-# OVERLAPS #-}
    ( ApplyFunctionToHomogeneousSum srest trest (s -> t)
    ) => ApplyFunctionToHomogeneousSum (s :+: srest) (t :+: trest) (s -> t)
  where
    applyFunctionToHomogeneousSum f (Sum sum) = case sum of
        Left l -> Sum (Left (f l))
        Right r -> Sum (Right (applyFunctionToHomogeneousSum f r))
