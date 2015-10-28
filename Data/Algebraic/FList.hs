{-|
Module      : Data.FList
Description : Definition of FList, describing a list of functions.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}

module Data.Algebraic.FList (

      FList
    , FListAsFunction
    , MakeFList
    , makeFList
    , AutoFList
    , autoFList
    , AutoFListParameters
    , AutoFListCodomain
    , AutoFListCodomainFunctor

    ) where

import Data.Proxy
import Data.Algebraic.MapThroughArrows

-- | An FList holds 0 or more functions with codomain @t@. Domainds are
--   indicated by the list type parameter.
data FList (ps :: [*]) (t :: *) where
    FListZ :: FList '[] t
    FListS :: (p -> t) -> FList ps t -> FList (p ': ps) t

-- | Identifies a singleton type list.
type family IsSingleton (ps :: [*]) :: Bool where
    IsSingleton '[p] = 'True
    IsSingleton (p ': q ': ps) = 'False

-- | Produce a function with as many arrows as there are elements of @ps@.
--   A @t@ follows the rightmost arrow, if any.
--
--     @
--       FListAsFunction [p_1, .., p_n] t =
--              (p_1 -> t)
--           -> (p_2 -> t)
--           -> ..
--           -> (p_n -> t)
--           -> t
--     @
--
type family FListAsFunction (ps :: [*]) (t :: *) (r :: *) :: * where
    FListAsFunction '[] t r = r
    FListAsFunction (p ': ps) t r = (p -> t) -> FListAsFunction ps t r


-- | Here we describe how to pull an FList out of thin air.
--   It's convenient to put he FList behind some applicative, so we do that.
--
--   > (p_1 -> t) -> .. -> (p_n -> t) -> a (FList [p_1 .. p_n] t)
--
class MakeFList (b :: Bool) (ps :: [*]) (t :: *) (a :: * -> *) where
    makeFList
        :: Proxy b
        -> Proxy ps
        -> Proxy t
        -> Proxy a
        -> FListAsFunction ps t (a (FList ps t))

instance {-# OVERLAPS #-} Applicative a => MakeFList 'True '[p] t a where
    makeFList _ _ _ _ = \f -> pure (FListS f FListZ)

instance {-# OVERLAPS #-}
    ( MakeFList (IsSingleton ps) ps t a
    , f ~ FListAsFunction ps t (a (FList ps t))
    , g ~ FListAsFunction ps t (a (FList (p ': ps) t))
    , MapThroughArrows f g (a (FList ps t)) (a (FList (p ': ps) t))
    , Functor a
    ) => MakeFList 'False (p ': ps) t a
  where
    makeFList _ _ proxyT proxyA = \f ->
        let 
            extendFList :: a (FList ps t) -> a (FList (p ': ps) t)
            extendFList = fmap (FListS f)
            proxyB :: Proxy (IsSingleton ps)
            proxyB = Proxy
            proxyPS :: Proxy ps
            proxyPS = Proxy
        in  mapThroughArrows (extendFList) (makeFList proxyB proxyPS proxyT proxyA)

-- | This class allows us to create the FList function without proxies.
class AutoFList f where
    autoFList :: f

-- | Should be such that
--   > AutoFListParameters (FListAsFunction ps t r) = ps
type family AutoFListParameters (f :: *) :: [*] where
    AutoFListParameters ((p -> t) -> r) = p ': AutoFListParameters r
    AutoFListParameters r = '[]

type family AutoFListCodomain (f :: *) :: * where
    AutoFListCodomain ((p -> t) -> r) = AutoFListCodomain r
    AutoFListCodomain (a (FList ps t)) = t

type family AutoFListCodomainFunctor (f :: *) :: (* -> *) where
    AutoFListCodomainFunctor ((p -> t) -> r) = AutoFListCodomainFunctor r
    AutoFListCodomainFunctor (a (FList ps t)) = a

instance
    ( MakeFList (IsSingleton (AutoFListParameters f)) (AutoFListParameters f) (AutoFListCodomain f) (AutoFListCodomainFunctor f)
    , f ~ FListAsFunction
              (AutoFListParameters f)
              (AutoFListCodomain f)
              (AutoFListCodomainFunctor f (FList (AutoFListParameters f) (AutoFListCodomain f)))
    ) => AutoFList f
  where
    autoFList = makeFList proxyB proxyPS proxyT proxyA
      where
        proxyB :: Proxy (IsSingleton (AutoFListParameters f))
        proxyB = Proxy
        proxyPS :: Proxy (AutoFListParameters f)
        proxyPS = Proxy
        proxyT :: Proxy (AutoFListCodomain f)
        proxyT = Proxy
        proxyA :: Proxy (AutoFListCodomainFunctor f)
        proxyA = Proxy
