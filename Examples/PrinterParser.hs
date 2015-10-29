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
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Examples.PrinterParser where

import Prelude hiding ((.), id)
import Control.Arrow
import Control.Category
import Data.Proxy
import Data.Algebraic.Function
import Data.Algebraic.Function.GLB
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

example4 = parserPrinterOfSum (example1 .*. example1)

-- Try parsing "(hello"). Notice how you get two cases!
parseEx4 :: String -> [(() :+: (), String)]
parseEx4 str = runKleisli (from example4) ((), str)

example5 = parserPrinterOfProduct (example1 .*. example1)

example6 = parserPrinterOfSum (example1 .*. example5)


-- | Product of printer/parsers to printer/parser of product.
--
--      F f1 g1 (p1, String) ((), String) :*: ... :*: F fn gn (pn, String) ((), String)
--   -> F (GLBOfAll fs) (GLBOfAll gs) ((p1 :*: ... :*: pn), String) ((), String)
--
class ParserPrinterOfProduct product p stream | product -> p, product -> stream where
    parserPrinterOfProduct
        :: product
        -> F (GLBFold (ProductTos product))
             (GLBFold (ProductFroms product))
             (p, stream)
             ((), stream)

instance {-# OVERLAPS #-}
    (
    ) => ParserPrinterOfProduct (F f g (p, stream) ((), stream)) p stream
  where
    parserPrinterOfProduct = id

instance {-# OVERLAPS #-}
    ( Arrow (GLBFold (ProductTos rest))
    , Arrow (GLBFold (ProductFroms rest))
    -- TODO clean this up. Use ParserPrinterOfSum for reference.
    , Composable (GLBFold (ProductTos rest)) Bijection
    , Composable (GLBFold (ProductFroms rest)) Bijection
    , Composable f (GLBFold (ProductTos rest))
    , Composable g (GLBFold (ProductFroms rest))
    , Composable f Total
    , Composable g Bijection
    , Composable (GLB f Bijection) (GLBFold (ProductTos rest))
    , Composable (GLB g Bijection) (GLBFold (ProductFroms rest))
    , ParserPrinterOfProduct rest prest stream
    ) => ParserPrinterOfProduct ((F f g (p, stream) ((), stream)) :*: rest)
                                (p :*: prest)
                                stream
  where
    parserPrinterOfProduct (Product (a, b)) =
        -- Here we just have to juggle the input and output. We find prest,
        -- feed it to the recursive part while passing p on, then feed
        -- p to the top of the product and we're done.
        let recursive :: F (GLBFold (ProductTos rest))
                           (GLBFold (ProductFroms rest))
                           (prest, stream)
                           ((), stream)
            recursive = parserPrinterOfProduct b

            disassemble :: F Total
                             Bijection
                             (p :*: prest, stream)
                             (p, (prest, stream))
            disassemble = F (arr (\(Product (p, prest), stream) -> (p, (prest, stream))))
                            (arr (\(p, (prest, stream)) -> (Product (p, prest), stream)))

            reassemble :: F (GLB f Total)
                            (GLB g Bijection)
                            (p, ((), stream))
                            ((), stream)
            reassemble = a <.> aux1

            aux1 :: F Total Bijection (p, ((), stream)) (p, stream)
            aux1 = F (arr (\(p, ((), stream)) -> (p, stream)))
                     (arr (\(p, stream) -> (p, ((), stream))))

        in  reassemble <.> useBottomOfProduct recursive <.> disassemble

-- | Product of printer/parsers to printer/parser of a corresponding sum.
--
--      F f1 g1 (s1, String) ((), String) :+: ... :+: F fn gn (sn, String) ((), String)
--   -> F (GLBOfAll fs)
--        (GLB (GLBOfAll gs) Surjection)
--        ((s1 :+: ... :+: sn), String)
--        ((), String)
--
--   Notice how we throw Surjection there, onto the GLB of the gs. That's true
--   only for sums of size > 1, because that case must use a Surjection.
--   Intuitively, it's because when we want to invert, we must try all
--   alternatives.
--
class ParserPrinterOfSum product sum stream | product -> sum, product -> stream where
    parserPrinterOfSum
        :: product
        -> F (GLBFold (ProductTos product))
             (GLB (GLBFold (ProductFroms product)) (SumGLBModifier product))
             (sum, stream)
             ((), stream)

type family SumGLBModifier (product :: *) :: * -> * -> * where
    SumGLBModifier (p :*: q) = Surjection
    SumGLBModifier p = Bijection

type family TagSumWithStream (sum :: *) (stream :: *) :: * where
    TagSumWithStream (s :+: rest) stream = (s, stream) :+: TagSumWithStream rest stream
    TagSumWithStream s stream = (s, stream)

class TagSumWithStreamC sum stream where
    tagSumWithStream :: F Total
                          Bijection
                          (sum, stream)
                          (TagSumWithStream sum stream)

instance {-# OVERLAPS #-}
    ( TagSumWithStream s stream ~ (s, stream)
    ) => TagSumWithStreamC s stream
  where
    tagSumWithStream = F id id

instance {-# OVERLAPS #-}
    ( TagSumWithStreamC rest stream
    ) => TagSumWithStreamC (s :+: rest) stream
  where
    tagSumWithStream = reassemble
                     . work
                     . disassemble

      where
        reassemble :: F Total
                        Bijection
                        (Either (s, stream) (TagSumWithStream rest stream))
                        (TagSumWithStream (s :+: rest) stream)
        reassemble = F fto ffrom
          where
            fto :: Total (Either (s, stream) (TagSumWithStream rest stream))
                         (TagSumWithStream (s :+: rest) stream)
            fto = arr $ \either -> case either of
                            Left (s, stream) -> Sum (Left (s, stream))
                            Right rest -> Sum (Right rest)
            ffrom :: Bijection (TagSumWithStream (s :+: rest) stream)
                               (Either (s, stream) (TagSumWithStream rest stream))
            ffrom = arr $ \tagged -> case tagged of
                              Sum (Left l) -> Left l
                              Sum (Right r) -> Right r

        work :: F Total
                  Bijection
                  (Either (s, stream) (rest, stream))
                  (Either (s, stream) (TagSumWithStream rest stream))
        work = F fto ffrom
          where
            fto :: Total (Either (s, stream) (rest, stream))
                         (Either (s, stream) (TagSumWithStream rest stream))
            fto = right (to tagSumWithStream)
            ffrom :: Bijection (Either (s, stream) (TagSumWithStream rest stream))
                               (Either (s, stream) (rest, stream))
            ffrom = right (from tagSumWithStream)

        disassemble :: F Total
                         Bijection
                         (s :+: rest, stream)
                         (Either (s, stream) (rest, stream))
        disassemble = F fto ffrom
          where
            fto :: Total (s :+: rest, stream) (Either (s, stream) (rest, stream))
            fto = arr $ \(Sum sum, stream) -> case sum of
                            Left l -> Left (l, stream)
                            Right r -> Right (r, stream)
            ffrom :: Bijection (Either (s, stream) (rest, stream)) (s :+: rest, stream)
            ffrom = arr $ \sum -> case sum of
                              Left (l, stream) -> (Sum (Left l), stream)
                              Right (r, stream) -> (Sum (Right r), stream)


type family SumOutput (sum :: *) (stream :: *) :: * where
    SumOutput (s :+: rest) stream = ((), stream) :+: SumOutput rest stream
    SumOutput s stream = ((), stream)

instance {-# OVERLAPS #-}
    (
    ) => ParserPrinterOfSum (F f g (summand, stream) ((), stream)) 
                            summand
                            stream
  where
    parserPrinterOfSum = id

instance
    ( ArrowChoice f
    , ArrowChoice g
    -- For work <.> prepare
    , Composable (GLBFold (ProductTos ((F f g (s, stream) ((), stream)) :*: rest))) Total
    , Composable (GLBFold (ProductFroms ((F f g (s, stream) ((), stream)) :*: rest))) Bijection
    -- For finish <.> work
    , Composable Total (GLB (GLBFold (ProductTos ((F f g (s, stream) ((), stream)) :*: rest))) Total)
    , Composable Surjection (GLB (GLBFold (ProductFroms ((F f g (s, stream) ((), stream)) :*: rest))) Bijection)

    -- Match output types.
    ,   (GLBFold (ProductTos ((F f g (s, stream) ((), stream)) :*: rest)))
      ~ GLB Total (GLB (GLBFold (ProductTos ((F f g (s, stream) ((), stream)) :*: rest))) Total)
    ,   (GLB (GLBFold (ProductFroms ((F f g (s, stream) ((), stream)) :*: rest))) (SumGLBModifier ((F f g (s, stream) ((), stream)) :*: rest)))
      ~ GLB Surjection (GLB (GLBFold (ProductFroms ((F f g (s, stream) ((), stream)) :*: rest))) Bijection)

    , SumF' ((F f g (s, stream) ((), stream)) :*: rest)
            (TagSumWithStream (s :+: srest) stream)
            (SumOutput (s :+: srest) stream)

    , FoldSum (SumOutput (s :+: srest) stream) ((), stream)
    , HomogeneousSumPreimage (SumOutput (s :+: srest) stream) ((), stream)
    , TagSumWithStreamC (s :+: srest) stream
    , ParserPrinterOfSum rest srest stream 
    ) => ParserPrinterOfSum ((F f g (s, stream) ((), stream)) :*: rest)
                            (s :+: srest)
                            stream
  where
    parserPrinterOfSum product =
        let
            work :: F (GLBFold (ProductTos ((F f g (s, stream) ((), stream)) :*: rest)))
                      (GLBFold (ProductFroms ((F f g (s, stream) ((), stream)) :*: rest)))
                      (TagSumWithStream (s :+: srest) stream)
                      (SumOutput (s :+: srest) stream)
            work = sumF' product

            -- We pass a sum of ((), stream) through this to give a single
            -- ((), stream).
            finish :: F Total
                        Surjection
                        (SumOutput (s :+: srest) stream)
                        ((), stream)
            finish = F fto ffrom
              where
                fto :: Total (SumOutput (s :+: srest) stream) ((), stream)
                fto = arr foldSum
                ffrom :: Surjection ((), stream) (SumOutput (s :+: srest) stream)
                ffrom = Kleisli homogeneousSumPreimage

            -- Still not there... must make a term which takes the stream and tags
            -- the summand with it.
            prepare :: F Total
                         Bijection
                         (s :+: srest, stream)
                         (TagSumWithStream (s :+: srest) stream)
            prepare = tagSumWithStream

        in  finish <.> work <.> prepare

-- TODO move this back to Function.hs, after bringing GLB.hs with it.
class SumF' product s t where
    sumF' 
        :: product
        -> F (GLBFold (ProductTos product))
             (GLBFold (ProductFroms product))
             s
             t

instance {-# OVERLAPS #-}
    (
    ) => SumF' (F f g s t) s t
  where
    sumF' = id

instance {-# OVERLAPS #-}
    ( ArrowChoice f
    , ArrowChoice g
    , ArrowChoice (GLBFold (ProductTos rest))
    , ArrowChoice (GLBFold (ProductFroms rest))
    -- These are for work <.> disassemble
    , Composable (GLBFold (ProductTos rest)) Total
    , Composable (GLBFold (ProductFroms rest)) Bijection
    -- These are for reassemble <.> work <.> disassemble
    , Composable f (GLBFold (ProductTos rest))
    , Composable g (GLBFold (ProductFroms rest))

    , SumF' rest srest trest
    ) => SumF' ((F f g s t) :*: rest) (s :+: srest) (t :+: trest)
  where
    sumF' (Product (a, b)) =
        let recursive :: F (GLBFold (ProductTos rest))
                           (GLBFold (ProductFroms rest))
                           (srest)
                           (trest)
            recursive = sumF' b

            work :: F (GLBFold (ProductTos rest))
                      (GLBFold (ProductFroms rest))
                      (Either s srest)
                      (Either s trest)
            work = useBottomOfSum recursive

            disassemble
                :: F Total
                     Bijection
                     (s :+: srest)
                     (Either s srest)
            disassemble = disassembleSum

            reassemble
                :: F f
                     g
                     (Either s trest)
                     (t :+: trest)
            reassemble = reassembleSum a

        in  reassemble <.> work <.> disassemble
