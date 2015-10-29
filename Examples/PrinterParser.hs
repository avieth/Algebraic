{-|
Module      : Examples.PrinterParser
Description : Example of simultaneously-defined printers and parsers.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE Arrows #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Examples.PrinterParser where

import Prelude hiding ((.), id)
import Control.Arrow
import Control.Category
import Data.Proxy
import Data.Algebraic.Function
import Data.Algebraic.Product
import Data.Algebraic.Sum

class Stream stream token where
    streamTake :: stream -> Maybe (token, stream)
    streamPut :: token -> stream -> stream

instance Stream [t] t where
    streamTake ts = case ts of
        (x : xs) -> Just (x, xs)
        _ -> Nothing
    streamPut = (:)

anyToken
    :: forall stream token .
       ( Stream stream token )
    => Proxy stream
    -> F Total Injection (token, stream) ((), stream)
anyToken _ = F fto ffrom
  where
    fto :: Total (token, stream) ((), stream)
    fto = arr (\(token, stream) -> ((), streamPut token stream))
    ffrom :: Partial ((), stream) (token, stream)
    ffrom = Kleisli (\(_, stream) -> streamTake stream)

token
    :: forall stream token .
       ( Eq token
       , Stream stream token
       )
    => Proxy stream
    -> token
    -> F Total Injection ((), stream) ((), stream)
token _ token = F fto ffrom
  where
    fto :: Total ((), stream) ((), stream)
    fto = arr (\((), stream) -> ((), streamPut token stream))
    ffrom :: Partial ((), stream) ((), stream)
    ffrom = Kleisli $ \(_, str) -> case streamTake str of
        Just (token', rest) -> if token == token' then Just ((), rest) else Nothing
        _ -> Nothing

string
    :: forall stream token .
       ( Eq token
       , Stream stream token
       )
    => Proxy stream
    -> [token]
    -> F Total Injection ((), stream) ((), stream)
string stream tokens = mconcat (fmap (token stream) tokens)

many
    :: ( ArrowApply f
       , ArrowApply g
       )
    => F f g a b
    -> F f g [a] [b]
many = throughTraversable

-- Example 1: print/parse things sequentially.
example1 = token stream '(' `fcompose` string stream "hello" `fcompose` token stream ')'
  where
    stream :: Proxy String
    stream = Proxy

-- Example 2: print/parse a product (sequentially parse its components).
-- We use productF to pull a product of F's into an F of products.
example2 = productF (example1 .*. example1)

-- Example 3: example 2, but to parse you need only give a single unit.
example3 = sequenceProduct (example1 .*. example1)

-- Example 4: print/parse alternatives.
-- Here we have an ambiguous parser: it'll pick up (hello) or (hello)(hello)
example4 = totalSurjectionOfHomogeneousSum `fcompose` sumF (example1 .*. example3)
