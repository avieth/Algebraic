{-|
Module      : Data.Index
Description : Definition of nat-indices.
Copyright   : (c) Alexander Vieth, 2015
Licence     : BSD3
Maintainer  : aovieth@gmail.com
Stability   : experimental
Portability : non-portable (GHC only)
-}

{-# LANGUAGE AutoDeriveTypeable #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Algebraic.Index (

      Index(..)
    , one
    , two
    , three
    , four
    , five
    , six
    , seven
    , eight
    , nine
    , ten

    ) where

import GHC.TypeLits
import Data.Proxy

data Index (n :: Nat) = Index

instance KnownNat n => Show (Index n) where
    show idx = show (natVal (Proxy :: Proxy n))

one :: Index 1
one = Index

two :: Index 2
two = Index

three :: Index 3
three = Index

four :: Index 4
four = Index

five :: Index 5
five = Index

six :: Index 6
six = Index

seven :: Index 7
seven = Index

eight :: Index 8
eight = Index

nine :: Index 9
nine = Index

ten :: Index 10
ten = Index
