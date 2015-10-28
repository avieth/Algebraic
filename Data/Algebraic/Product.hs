{-|
Module      : Data.Algebraic.Product
Description : Algebraic datatype products.
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

module Data.Algebraic.Product (

      Product(..)
    , (:*:)
    , (.*.)
    , Component
    , getComponent
    , Sub
    , Project
    , project
    , sub
    , Size
    , Construct
    , Reconstruct
    , ConstructProduct
    , ReconstructProduct
    , constructProduct
    , reconstructProduct
    , EliminateTerm
    , IntroduceTerm
    , SwapTerms
    , SwapTermsNormalize
    , SwapTerms_
    , ReplaceTerm
    , ReplaceTermF
    , replaceTerm
    , FoldProduct
    , foldProduct

    ) where

-- TODO named fields (not just Nat-indexed) to simulate records, and then
-- lens-like get/set/update infrastructure.
-- NB we will have to export the Component constructor, so that invertible
-- syntax can use it.
--
--   data Index (n :: Nat) = Index
--   data Record (s :: Symbol) = Record
--   data Field (s :: Symbol) t = Field t
--
--   instance Project (Index 1) (Product p q)
--   instance Project (Index 1) p
--   instance Project (Index (n-1)) q => Project (Index n) (Product p q)
--   instance Project (Record s) (Product (Field s t) q)
--   instance Project (Record s) (Field s t)
--   instance Project (Record s) q => Project (Record s) (Product p q)
--
--   type family NoDuplicateFeildNames p where
--       NoDuplicateFieldNames (Product (Field name t) q) =
--           And
--           (NoFieldName name q)
--           (NoDuplicateFieldNames q)
--       NoDuplicateFieldNames (Product p q) =
--           NoDuplicateFieldNames q
--       NoDuplicateFieldNames (Field name t) = True
--       NoDuplicateFieldNames p = True
--
-- So then we work with types like
--
--   Field "foo" Bool :*: Field "bar" Bool :*: ()
--
-- We can always index by Nat; we can sometimes index by Symbol.
-- Cool.
--
-- As for the end goal: simple and safe invertible syntax... 
-- Well, before we can do that, we must consider invertible functions in
-- general. How can this Product help us to construct them?
--
--   1. If we have an invertible function for each component p_n |-> q_n
--      then we have an invertible function to a same-sized product, p's
--      replaced by q's.
--   2. We can also make an invertible function to a monoid, if all q_n are
--      the same. Throw each one into the free monoid then mconcat it.

import GHC.TypeLits
import Data.Proxy
import Data.Algebraic.Index
import Data.Algebraic.MapThroughArrows
import Data.Semigroup (Semigroup, (<>))

newtype Product a b = Product (a, b)

instance {-# OVERLAPS #-}
    ( Show a
    , Show b
    ) => Show (Product a b)
  where
    show (Product (a, b)) = concat [
          "("
        , show a
        , ") x ("
        , show b
        , ")"
        ]

instance {-# OVERLAPS #-}
    ( Show a
    , Show (Product b c)
    ) => Show (Product a (Product b c))
  where
    show (Product (a, Product b)) = concat [
          "("
        , show a
        , ") x "
        , show (Product b)
        ]


type a :*: b = Product a b
infixr 8 :*:

(.*.) :: a -> b -> Product a b
a .*. b = Product (a, b)
infixr 8 .*.

newtype Component p n = Component {
     getComponent :: Sub p n
   }

type family Sub (p :: *) (n :: Nat) :: * where
    Sub (Product a b) 1 = a
    Sub a 1 = a
    Sub (Product a b) n = Sub b (n - 1)

class Project p n where
    project :: Index n -> p -> Component p n

instance {-# OVERLAPS #-} Sub b 1 ~ b => Project b 1 where
    project _ b = Component b

instance {-# OVERLAPS #-} Project (Product a b) 1 where
    project _ (Product (a, _)) = Component a

instance {-# OVERLAPS #-}
    ( Project b (n - 1)
    -- This constraint: we know it's always true (just look at the definition
    -- of Sub) but apparently GHC does not know it's always true.
    , Sub b (n - 1) ~ Sub (Product a b) n
    ) => Project (Product a b) n
  where
    project _ (Product (_, b)) =
        let cmp :: Component b (n - 1)
            cmp = project (Index :: Index (n - 1)) b
            sub' :: Sub b (n - 1)
            sub' = getComponent cmp
        in  Component sub'

sub :: Project p n => p -> Index n -> Sub p n
sub p n = getComponent (project n p)

type family Size (p :: *) :: Nat where
    Size (Product a b) = 1 + Size b
    Size b = 1

type family Construct (p :: *) (q :: *) :: * where
    Construct (Product a b) q = a -> Construct b q
    Construct b q = b -> q

-- | Like construct, but for constructing a product from its components.
--   We use the nat index to ensure that only the proper component is used at
--   each place.
--
--     Reconstruct p q n
--
--   is the function returning @q@ using nat-indexed components of @q@ starting
--   at @n@. @p@ is there only to determine when to stop recursion.
--   So we're principally interested in
--
--     Reconstruct p p 1
type family Reconstruct (p :: *) (q :: *) (n :: Nat) :: * where
    Reconstruct (Product a b) q n = Component q n -> Reconstruct b q (n + 1)
    Reconstruct b q n = Component q n -> q

class ConstructProductWithProxy p q where
    constructProductWithProxy :: Proxy p -> Proxy q -> Construct p q

instance {-# OVERLAPS #-} (Construct p p ~ (p -> p)) => ConstructProductWithProxy p p where
    constructProductWithProxy _ _ = id

instance {-# OVERLAPS #-}
    ( ConstructProductWithProxy b b
    , Construct (Product a b) (Product a b) ~ (a -> Construct b (Product a b))
    , MapThroughArrows (Construct b b)
                       (Construct b  (Product a b))
                       (b)
                       (Product a b)
    ) => ConstructProductWithProxy (Product a b) (Product a b)
  where
    constructProductWithProxy _ _ = \a -> mapThroughArrows
        ((\b -> Product (a, b)) :: b -> Product a b)
        (constructProductWithProxy proxyB proxyB :: Construct b b)
      where
        proxyB :: Proxy b
        proxyB = Proxy

class ConstructProduct p where
    constructProduct :: Construct p p

instance
    ( ConstructProductWithProxy p p
    ) => ConstructProduct p
  where
    constructProduct = constructProductWithProxy (Proxy :: Proxy p) (Proxy :: Proxy p)

class BumpComponents f g q r x where
    bumpComponents :: Proxy q -> Proxy r -> Proxy x -> f -> g

-- We have a function @f@ which reconstructs some product @q@, i.e. 
--   f ~ Reconstruct q q 1
-- and we would like to extend it a function @g@ which reconstructs
--   r ~ (x :*: q)
-- so we need to bump up all of the component indices on the arguments of
-- @f@.
instance {-# OVERLAPS #-}
    ( Sub q n ~ Sub r (n + 1)
    , r ~ (x :*: q)
    , x ~ Sub r n
    , cmpQN ~ Component q n
    , cmpRN ~ Component r n
    , cmpRSN ~ Component r (n + 1)
    ) => BumpComponents (cmpQN -> q) (cmpRN -> cmpRSN -> r) q r x
  where
    bumpComponents _ _ _ f = \(cmpRN :: Component r n) (cmpRSN :: Component r (n + 1)) ->
        let q = f (Component (getComponent cmpRSN) :: Component q n)
        in  (getComponent cmpRN) .*. q

instance {-# OVERLAPS #-}
    ( Sub q n ~ Sub r (n + 1)
    , r ~ (x :*: q)
    , x ~ Sub r n
    , cmpQN ~ Component q n
    , cmpRN ~ Component r n
    , cmpRSN ~ Component r (n + 1)
    , BumpComponents qrest (cmpRSN -> rrest) q r (Sub r (n + 1))
    , MapThroughArrows (Component (x :*: q) (n + 1) -> rrest)
                       (rrest)
                       (q)
                       (x :*: q)
    ) => BumpComponents (cmpQN -> qrest) (cmpRN -> cmpRSN -> rrest) q r x
  where
    bumpComponents proxyQ proxyR _ f = \(cmpRN :: Component r n) (cmpRSN :: Component r (n + 1)) ->
        let restq = f (Component (getComponent cmpRSN) :: Component q n)
            bumped :: cmpRSN -> rrest
            bumped = bumpComponents proxyQ proxyR (Proxy :: Proxy (Sub r (n + 1))) restq
            extendProduct :: q -> r
            extendProduct = \q -> (getComponent cmpRN) .*. q
        in  mapThroughArrows extendProduct bumped

class ReconstructProductWithProxy p q where
    reconstructProductWithProxy :: Proxy p -> Proxy q -> Reconstruct p q 1

instance {-# OVERLAPS #-}
    ( Reconstruct p p 1 ~ (Component p 1 -> p)
    , p ~ Sub p 1
    ) => ReconstructProductWithProxy p p
  where
    reconstructProductWithProxy _ _ = getComponent

instance {-# OVERLAPS #-}
    ( ReconstructProductWithProxy b b
    , BumpComponents (Reconstruct b b 1)
                     (Component (Product a b) 1 -> Reconstruct b (Product a b) 2)
                     (b)
                     (Product a b)
                     (a)
    ) => ReconstructProductWithProxy (Product a b) (Product a b)
  where
    reconstructProductWithProxy _ _ = \(cmp :: Component (Product a b) 1) ->
        let lower :: Reconstruct b b 1
            lower = reconstructProductWithProxy (Proxy :: Proxy b) (Proxy :: Proxy b)
            bumped :: Reconstruct (Product a b) (Product a b) 1
            bumped = bumpComponents (Proxy :: Proxy b)
                                    (Proxy :: Proxy (Product a b))
                                    (Proxy :: Proxy a)
                                    lower
        in  bumped cmp

class ReconstructProduct p where
    reconstructProduct :: Proxy p -> Reconstruct p p 1

instance
    ( ReconstructProductWithProxy p p
    ) => ReconstructProduct p
  where
    reconstructProduct proxyP = reconstructProductWithProxy proxyP proxyP

type family EliminateTerm product (index :: Nat) where
    EliminateTerm (p :*: rest) 1 = rest
    EliminateTerm (p :*: q :*: rest) n = p :*: EliminateTerm (q :*: rest) (n - 1)
    EliminateTerm (p :*: q) 2 = p
    EliminateTerm (p :*: rest) n = p :*: EliminateTerm rest (n - 1)
    EliminateTerm p 1 = ()

type family IntroduceTerm r product (index :: Nat) where
    IntroduceTerm r (p :*: rest) 1 = r :*: p :*: rest
    IntroduceTerm r (p :*: rest) 2 = p :*: r :*: rest
    IntroduceTerm r (p :*: rest) n = p :*: IntroduceTerm r rest (n - 1)
    IntroduceTerm r p 2 = p :*: r
    IntroduceTerm r p 1 = r :*: p

type family SwapTerms product (idx1 :: Nat) (idx2 :: Nat) where
    SwapTerms p n n = p
    SwapTerms (a :*: b :*: c) idx1 idx2 = SwapTermsNormalize (a :*: b :*: c) idx1 idx2 (CmpNat idx1 idx2)
    SwapTerms (a :*: b) 1 2 = b :*: a
    SwapTerms (a :*: b) 2 1 = b :*: a

type family SwapTermsNormalize product (idx1 :: Nat) (idx2 :: Nat) (order :: Ordering) where
    SwapTermsNormalize p idx1 idx2 'LT = SwapTerms_ p idx1 idx2
    SwapTermsNormalize p idx1 idx2 'GT = SwapTerms_ p idx2 idx1

-- We assume idx1 < idx2
type family SwapTerms_ product (idx1 :: Nat) (idx2 :: Nat) where
    SwapTerms_ (p :*: q :*: r) 1 2 = q :*: p :*: r
    SwapTerms_ (p :*: q) 1 2 = q :*: p
    SwapTerms_ (p :*: q) 1 idx2 = (Sub (p :*: q) idx2) :*: (ReplaceTerm p q (idx2 - 1))
    SwapTerms_ (p :*: q) idx1 idx2 = p :*: (SwapTerms_ q (idx1 - 1) (idx2 - 1))

type family ReplaceTerm p product (idx2 :: Nat) where
    ReplaceTerm p (q :*: rest) 1 = (p :*: rest)
    ReplaceTerm p q 1 = p
    ReplaceTerm p (q :*: rest) idx2 = q :*: (ReplaceTerm p rest (idx2 - 1))

class ReplaceTermF p q (idx :: Nat) where
    replaceTerm :: p -> q -> Index idx -> ReplaceTerm p q idx

instance {-# OVERLAPS #-}
    (
    ) => ReplaceTermF p (q :*: rest) 1
  where
    replaceTerm p (Product (_, rest)) _ = p .*. rest

instance {-# OVERLAPS #-}
    ( ReplaceTerm p q 1 ~ p
    ) => ReplaceTermF p q 1
  where 
    replaceTerm p _ _ = p

instance {-# OVERLAPS #-}
    ( ReplaceTerm p (q :*: rest) idx2 ~ (q :*: (ReplaceTerm p rest (idx2 - 1)))
    , ReplaceTermF p rest (idx2 - 1)
    ) => ReplaceTermF p (q :*: rest) idx2
  where
    replaceTerm p (Product (q, rest)) _ = q .*. (replaceTerm p rest (Index :: Index (idx2 - 1)))

{-
 - Here's another way to do SwapTerms. I find it's not as useful, though,
 - since writing typeclasses against it is more difficult that the above
 - presentation.
type family SwapTerms product (index1 :: Nat) (index2 :: Nat) where
    SwapTerms p n n = p
    SwapTerms (a :*: b :*: c) idx1 idx2 = SwapTerms_ (a :*: b :*: c) idx1 idx2 (CmpNat idx1 idx2)
    SwapTerms (a :*: b) 1 2 = b :*: a
    SwapTerms (a :*: b) 2 1 = b :*: a

type family SwapTerms_ product (index1 :: Nat) (index2 :: Nat) (order :: Ordering) where
    -- idx1 < idx2
    -- In this case, we eliminate idx2 first, and then eliminate idx1 without
    -- the need to alter this index.
    -- Then, we reintroduce idx1 with the former thing at idx2, then
    -- reintroduce idx2
    SwapTerms_ product idx1 idx2 LT =
        IntroduceTerm 
            (Sub product idx1)
            (IntroduceTerm
                (Sub product idx2)
                (EliminateTerm (EliminateTerm product idx2) idx1)
                (idx1)
            )
            (idx2)

    SwapTerms_ product idx1 idx2 GT =
        IntroduceTerm 
            (Sub product idx2)
            (IntroduceTerm
                (Sub product idx1)
                (EliminateTerm (EliminateTerm product idx1) idx2)
                (idx2)
            )
            (idx1)
-}

-- | A homogeneous product of some semigroup can be collapsed into one value
--   of that semigroup.
class FoldProduct product t where
    foldProduct :: product -> t

instance {-# OVERLAPS #-} FoldProduct t t where
    foldProduct = id

instance {-# OVERLAPS #-}
    ( Semigroup t
    , FoldProduct rest t
    ) => FoldProduct (t :*: rest) t
  where
    foldProduct (Product (t, rest)) = t <> (foldProduct rest)
