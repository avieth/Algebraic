{-|
Module      : Data.Algebraic.MapThroughArrows
Description : Definition of the MapThroughArrows class.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.Algebraic.MapThroughArrows (

      MapThroughArrows
    , mapThroughArrows

    ) where

class MapThroughArrows f g s u where
    mapThroughArrows :: (s -> u) -> f -> g

instance {-# OVERLAPS #-} MapThroughArrows (s -> t) (s -> u) t u where
    mapThroughArrows = fmap

instance {-# OVERLAPS #-}
    ( MapThroughArrows q r t u
    ) => MapThroughArrows (s -> q) (s -> r) t u
  where
    mapThroughArrows f = fmap (mapThroughArrows f)
