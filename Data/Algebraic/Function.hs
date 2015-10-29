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
{-# LANGUAGE FunctionalDependencies #-}

module Data.Algebraic.Function (

      F(..)
    , ArrowHomomorphism
    , arrowHomomorphism
    , ArrowHomomorphismTyped(..)
    , ArrowHomomorphismType(..)
    , ArrowHomomorphismTypeF
    , ArrowHomomorphismGreatestLowerBound
    , ArrowHomomorphismGreatestLowerBoundParticular
    , relax
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
    , fcompose
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

-- | Must really be a homomorphism of arrows:
--
--     h (arr f) = arr f
--     h (first f) = first f
--     h (f . g) = h f . h g
--     h id = id
--
--   The first parameter is the domain, second is the codomain.
--
--   This class has just one instance. It relies upon ArrowHomomorphismTyped,
--   which takes an extra parameter so as to prevent overlap problems.
class
    ( Arrow f
    , Arrow g
    ) => ArrowHomomorphism f g
  where
    arrowHomomorphism :: forall s t . f s t -> g s t

instance
    ( Arrow f
    , Arrow g
    , ArrowHomomorphismTyped (ArrowHomomorphismTypeF f g) f g
    ) => ArrowHomomorphism f g
  where
    arrowHomomorphism = arrowHomomorphismTyped (Proxy :: Proxy (ArrowHomomorphismTypeF f g))

-- | We use this datatype and ArrowHomomorphismTypeF to disambiguate
--   homomorphism instances.
data ArrowHomomorphismType = AHToBottom | AHFromTop | AHReflexive | AHParticular

-- | This type family picks the homomorphism type. We identify four cases:
--   1. Homomorphisms to the bottom element (AHToBottom)
--   2. Homomorphisms from the top element (AHFromTop)
--   3. Homomorphisms from an element to itself (AHReflexive)
--   4. Particular homomorphisms (AHParticular)
--   The first 3 are given generically, and the last one must be given for
--   each non-bottom, non-top element of the order.
type family ArrowHomomorphismTypeF f g where
    ArrowHomomorphismTypeF a EmptyArrow = AHToBottom
    ArrowHomomorphismTypeF (Kleisli Identity) b = AHFromTop
    ArrowHomomorphismTypeF a a = AHReflexive
    ArrowHomomorphismTypeF a b = AHParticular

class
    ( Arrow f
    , Arrow g
    ) => ArrowHomomorphismTyped ty f g
  where
    arrowHomomorphismTyped :: Proxy ty -> (forall s t . f s t -> g s t)

instance {-# OVERLAPS #-} Arrow a => ArrowHomomorphismTyped AHReflexive a a where
    arrowHomomorphismTyped _ = id

-- | Kleisli Identity is the top element.
--
--     arrowHomomorphism (arr f)
--   = Kleisli $ return . runIdentity . runKleisli (arr f)
--   = Kleisli $ return
--   = arr f
--
--     arrowHomomorphism (first f)
--   = Kleisli $ return . runIdentity . runKleisli (first f)--   = Kleisli $ \(x, c) -> return (x, c)
--   = Kleisli $ \(x, c) -> return (x, c)
--   = first f
--
--     arrowHomomorphism id
--   = Kleisli $ return . runIdentity . runKleisli id
--   = Kleisli $ return
--   = id
--
--     arrowHomomorphism f . arrowHomomorphism g
--   = (Kleisli $ return . runIdentity . runKleisli f) . (Kleisli $ return . runIdentity . runKleisli g)
--   = Kleisli $ \x -> return (runIdentity (runKleisli g x)) >>= \y -> return (runIdentity (runKleisli f y))
--   = Kleisli $ \x -> \y -> return (runIdentity (runKleisli f (runIdentity (runKleisli g x))))
--   = ???
--   = Kleisli $ return . runIdentity . runKleisli (f . g)
--   = arrowHomomorphism (f . g)
--
instance {-# OVERLAPS #-} Arrow a => ArrowHomomorphismTyped AHFromTop (Kleisli Identity) a where
    arrowHomomorphismTyped _ kid = arr (runIdentity . runKleisli kid)

-- | EmptyArrow is the bottom element. This is obviously a homomorphism.
instance {-# OVERLAPS #-} Arrow a => ArrowHomomorphismTyped AHToBottom a EmptyArrow where
    arrowHomomorphismTyped _ _ = EmptyArrow

class
    ( Arrow g
    ) => ArrowHomomorphismSurjection g
  where
    arrowHomomorphismSurjection :: forall s t . Surjection s t -> g s t

instance
    (
    ) => ArrowHomomorphismSurjection Function
  where
    arrowHomomorphismSurjection kl = Kleisli $ toList . runKleisli kl

instance {-# OVERLAPS #-}
    ( ArrowHomomorphismSurjection a
    ) => ArrowHomomorphismTyped AHParticular Surjection a
  where
    arrowHomomorphismTyped _ = arrowHomomorphismSurjection

class
    ( Arrow g
    ) => ArrowHomomorphismInjection g
  where
    arrowHomomorphismInjection :: forall s t . Injection s t -> g s t

-- | Here we use the natural transformation Maybe ~> []
instance {-# OVERLAPS #-} ArrowHomomorphismInjection (Kleisli []) where
    arrowHomomorphismInjection kid = Kleisli $ \s -> case runKleisli kid s of
        Just x -> [x]
        Nothing -> []

instance {-# OVERLAPS #-}
    ( ArrowHomomorphismInjection a
    ) => ArrowHomomorphismTyped AHParticular Injection a
  where
    arrowHomomorphismTyped _ = arrowHomomorphismInjection

relax
    :: ( ArrowHomomorphism f1 f2
       , ArrowHomomorphism g1 g2
       )
    => F f1 g1 s t
    -> F f2 g2 s t
relax f = F (arrowHomomorphism (to f)) (arrowHomomorphism (from f))

-- The greatest lower bound is a commutative thing. We need to compute this:
--
--                     Kleisli Identity |Kleisli Maybe   |Kleisli NonEmpty|Kleisli []|...       |EmptyArrow
--                   +-------------------------------------------------------------------------------------
--   Kleisli Identity| Kleisli Identity |Kleisli Maybe   |Kleisli NonEmpty|Kleisli []|...       |EmptyArrow
--   Kleisli Maybe   | Kleisli Maybe    |Kleisli Maybe   |Kleisli []      |Kleisli []|...       |EmptyArrow
--   Kleisli NonEmpty| Kleisli NonEmpty |Kleisli NonEmpty|Kleisli NonEmpty|Kleisli []|...       |EmptyArrow
--   Kleisli []      | Kleisli []       |Kleisli []      |Kleisli []      |Kleisli []|...       |EmptyArrow
--   ...             | ...              |...             |...             |...       |...       |EmptyArrow
--   EmptyArrow      | EmptyArrow       |EmptyArrow      |EmptyArrow      |EmptyArrow|EmptyArrow|EmptyArrow
--
-- The presence of (...) means we need an open type family; we must be able to
-- add new entries to the lattice. But we must also avoid any type family
-- overlap. This can be done by giving only the lower-left half of the table
-- (it's commutative) and giving a type family which indicates which section
-- of the table we're in:
--    1. Leftmost column
--    2. Bottom row
--    3. Diagonal
--    4. Lower-left half (excluding diagonal)
--    5. Upper-right half (excluding diagonal)
-- One way to do this is to have each type determine a unique natural number,
-- or a symbol meaning infinity (for the EmptyArrow). This determines the
-- order of the rows (or columns, but we choose rows). Then we're in the
-- lower-left whenever the first index is greater than the second index, and
-- similar index-based rules for the other cases.
-- We demand particular instances for the lower-left half excluding the
-- diagonal and the leftmost and bottom rows. That's to say: the n'th
-- arrow must give its GLB with all of the earlier arrows (n-1)'th, (n-2)'th
-- excluding the 0'th (Kleisli Identity).
--
-- Injective type family use case? I think so! But do we *need* injective
-- type families? Data families are injective, but we can't use those, because
-- we need to go to some existing type Nat+Infinity.
-- Functional dependencies are tempting. Can they help us? Yes, but it's a hack.

type family ArrowGLBOrderT (f :: * -> * -> *)

-- Until we can assert that ArrowGLBOrderT is injective, we use a hack:
-- demand that every member of the order is an instance of this class, and
-- let the functional dependency and the class constraint do their work!
--
-- With injective type families, we can delete the ArrowGLBOrder class and
-- its instances.
class
    ( ArrowGLBOrderT ty ~ idx
    ) => ArrowGLBOrder (ty :: * -> * -> *) idx | idx -> ty

type instance ArrowGLBOrderT (Kleisli Identity) = (Finite 0)
type instance ArrowGLBOrderT (Kleisli Maybe) = (Finite 1)
type instance ArrowGLBOrderT (Kleisli NonEmpty) = (Finite 2)
type instance ArrowGLBOrderT (Kleisli []) = (Finite 3)
type instance ArrowGLBOrderT (EmptyArrow) = (Infinity)

instance ArrowGLBOrder (Kleisli Identity) (Finite 0)
instance ArrowGLBOrder (Kleisli Maybe) (Finite 1)
instance ArrowGLBOrder (Kleisli NonEmpty) (Finite 2)
instance ArrowGLBOrder (Kleisli []) (Finite 3)
instance ArrowGLBOrder (EmptyArrow) (Infinity)

data CommutativeTableSection = Leftmost | Bottom | Diagonal | LowerLeft | UpperRight

type family CommutativeArrowGLBOrder (f :: * -> * -> *) :: k where
    CommutativeArrowGLBOrder f = ArrowGLBOrderT f

type family CommutativeTableSectionF (f :: * -> * -> *) (g :: * -> * -> *) :: CommutativeTableSection where
    CommutativeTableSectionF f g = CommutativeTableSectionFStage1 (ArrowGLBOrderT f) (ArrowGLBOrderT g)

type family CommutativeTableSectionFStage1 (a :: k) (b :: l) :: CommutativeTableSection where
    CommutativeTableSectionFStage1 a a = Diagonal
    CommutativeTableSectionFStage1 (Finite 0) b = Leftmost
    CommutativeTableSectionFStage1 a (Finite 0) = Leftmost
    CommutativeTableSectionFStage1 Infinity b = Bottom
    CommutativeTableSectionFStage1 a Infinity = Bottom
    CommutativeTableSectionFStage1 n m  = CommutativeTableSectionFStage2 (OrderCompare n m)

type family CommutativeTableSectionFStage2 (order :: Ordering) :: CommutativeTableSection where
    CommutativeTableSectionFStage2 EQ = Diagonal
    CommutativeTableSectionFStage2 LT = UpperRight
    CommutativeTableSectionFStage2 GT = LowerLeft

type family ArrowHomomorphismGreatestLowerBound (g :: * -> * -> *) (h :: * -> * -> *) :: * -> * -> * where
    ArrowHomomorphismGreatestLowerBound g h =
        ArrowHomomorphismGreatestLowerBoundSectioned (CommutativeTableSectionF g h) g h

type family ArrowHomomorphismGreatestLowerBoundSectioned (section :: CommutativeTableSection) (f :: * -> * -> *) (g :: * -> * -> *) :: * -> * -> * where
    ArrowHomomorphismGreatestLowerBoundSectioned Diagonal f f = f
    ArrowHomomorphismGreatestLowerBoundSectioned Leftmost (Kleisli Identity) g = g
    ArrowHomomorphismGreatestLowerBoundSectioned Leftmost g (Kleisli Identity) = g
    ArrowHomomorphismGreatestLowerBoundSectioned Bottom (EmptyArrow) g = EmptyArrow
    ArrowHomomorphismGreatestLowerBoundSectioned Bottom g (EmptyArrow) = EmptyArrow
    ArrowHomomorphismGreatestLowerBoundSectioned UpperRight f g =
        ArrowHomomorphismGreatestLowerBoundSectioned LowerLeft g f
    ArrowHomomorphismGreatestLowerBoundSectioned LowerLeft f g =
        ArrowHomomorphismGreatestLowerBoundParticular f g

type family ArrowHomomorphismGreatestLowerBoundParticular (g :: * -> * -> *) (h :: * -> * -> *) :: * -> * -> *
type instance ArrowHomomorphismGreatestLowerBoundParticular (Kleisli NonEmpty) (Kleisli Maybe) = Kleisli []
type instance ArrowHomomorphismGreatestLowerBoundParticular (Kleisli []) (Kleisli NonEmpty) = Kleisli []
type instance ArrowHomomorphismGreatestLowerBoundParticular (Kleisli []) (Kleisli Maybe) = Kleisli []

-- I think the problem remains unsolved... Where does the SideChannel go in
-- the order? Makes no sense, since the SideChannel is parameterized by
-- another arrow which is presumably in the order.
--
-- We want to accomodate order homomorphisms: types h for which
--
--    GreatestLowerBound (h f) g
--  = GreatestLowerBound f (h g)
--  = GreatestLowerBound (h f) (h g)
--  = h (GreatestLowerBound f g)
--
-- But is it possible? ArrowHomomorphismGreatestLowerBound takes kind
-- * -> * -> *, not (* -> * -> *) -> * -> * -> *
--
-- Perhaps we could upgrade it...
--
--   newtype ArrowGLBIdentityHomomorphism f s t = f s t
--   newtype ArrowSideChannel m f s t = f (s, m) (t, m)

fcompose
    :: ( ArrowHomomorphism g1 (ArrowHomomorphismGreatestLowerBound g1 g2)
       , ArrowHomomorphism g2 (ArrowHomomorphismGreatestLowerBound g1 g2)
       , Category (ArrowHomomorphismGreatestLowerBound g1 g2)
       , ArrowHomomorphism h1 (ArrowHomomorphismGreatestLowerBound h1 h2)
       , ArrowHomomorphism h2 (ArrowHomomorphismGreatestLowerBound h1 h2)
       , Category (ArrowHomomorphismGreatestLowerBound h1 h2)
       )
    => F g2 h2 t u
    -> F g1 h1 s t
    -> F (ArrowHomomorphismGreatestLowerBound g1 g2)
         (ArrowHomomorphismGreatestLowerBound h1 h2)
         s
         u
fcompose left right = relax left . relax right

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
