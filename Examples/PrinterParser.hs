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
import Data.Algebraic.Function
import Data.Algebraic.Function.SideChannel

class Stream stream token where
    streamTake :: stream -> Maybe (token, stream)
    streamPut :: token -> stream -> stream

instance Stream [t] t where
    streamTake ts = case ts of
        (x : xs) -> Just (x, xs)
        _ -> Nothing
    streamPut = (:)

type Parser = SideChannel
type Printer = SideChannel

anyToken
    :: forall stream token .
       ( Stream stream token )
    => F (Printer stream Total) (Parser stream Partial) token ()
anyToken = F fto ffrom
  where
    fto :: Printer stream Total token ()
    fto = SideChannel (arr (\(token, stream) -> ((), streamPut token stream)))
    ffrom :: Parser stream Partial () token
    ffrom = SideChannel (Kleisli (\(_, stream) -> streamTake stream))

token
    :: forall stream token .
       ( Eq token
       , Stream stream token
       )
    => token
    -> F (Printer stream Total) (Parser stream Partial) () ()
token token = F fto ffrom
  where
    fto :: Printer stream Total () ()
    fto = SideChannel (arr (\((), stream) -> ((), streamPut token stream)))
    ffrom :: Parser stream Partial () ()
    ffrom = SideChannel . Kleisli $ \(_, str) -> case streamTake str of
        Just (token', rest) -> if token == token' then Just ((), rest) else Nothing
        _ -> Nothing

string
    :: forall stream token .
       ( Eq token
       , Stream stream token
       )
    => [token]
    -> F (Printer stream Total) (Parser stream Injection) () ()
string tokens = mconcat (fmap token tokens)

many
    :: ( ArrowApply f
       , ArrowApply g
       )
    => F f g a b
    -> F f g [a] [b]
many = throughTraversable
