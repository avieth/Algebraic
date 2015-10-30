Algebraic
=========

The goal of this experiment is to explore ways to construct functions
which are richer than the typical Haskell functions (of type `(->)`). In
particular, functions which are known to be bijective, or injective, or
surjective, or total, or partial, etc.

The foundation is this type, from [Data.Algebraic.Function](Data/Algebraic/Function.hs)

```Haskell
data F g h s t = F {
      to :: g s t
    , from :: h t s
    }
```

If `g` and `h` are arrows, then `F g h` is a category, so we can use it as
we would the typical function type `(->)`. Judiciously choosing types for
`g` and `h` gives rise to many familiar mathematical notions:

```Haskell
-- Total functions always produce a value...
type TotalFunction = F (Kleisli Identity) (EmptyArrow)

-- ... but partial functions do not.
-- Notice how the choice of EmptyArrow means we don't have to give any
-- information for the 'from' part of the definition.
type PartialFunction = F (Kleisli Maybe) (EmptyArrow)

-- Bijections can always be inverted...
type TotalBijection = F (Kleisli Identity) (Kleisli Identity)

-- ... injections can be inverted too, but not everything in the codomain
-- has a preimage.
type TotalInjection = F (Kleisli Identity) (Kleisli Maybe)

-- Surjections always give at least one preimage.
type TotalSurjection = F (Kleisli Identity) (Kleisli NonEmpty)
```

Functions of different types can be composed in such a way that the maximal
amount of information is preserved. For instance, if you compose a total
bijection with a total injection, you will get a total injection. This
is all supported by a very convenient ordering on the arrows in
question:

```
                    Kleisli Identity
                ^                      ^
               /                        \
              /                          \
             /                            \
          Kleisli Maybe          Kleisli NonEmpty
            ^         ^          ^         ^
            |          \        /          |
            |          Kleisli []          |
            |                              |
            \              ^               /
             \             |              /
              \                          /
                      EmptyArrow

```

In this diagram, there is a line from `x` to `y` if and only if there is
an arrow homomorphism from `y` to `x`. Notice the one in the middle:
`Kleisli []`. This is just a normal function: every image has 0 or more
preimages.

Really, we're concerned with the greatest-lower-bounds in this ordering,
which are captured by the type family `GLB` and the related class
`WitnessGLB`, instances of which are used to give:

```Haskell
fcompose
    :: forall f1 g1 f2 g2 s t u .
       ( Composable f1 f2
       , Composable g1 g2
       )
    => F f2 g2 u t
    -> F f1 g1 s u
    -> F (GLB f2 f1) (GLB g2 g1) s t
```

By using `(<.>)` as a replacement for the typical categorical composition
`(.)`, we allow GHC to infer the types of our functions.

```Haskell
plus :: Int -> F Total Bijection Int Int
plus i = F (arr ((+) i))
           (arr (\x -> x - i))

isPositive :: F Total Surjection Int Bool
isPositive = F (arr (\x -> x > 0))
               (Kleisli $ \b -> if b
                   then (1 :| [2..])
                   else fmap negate (0 :| [1..])
               )

boolNot :: F Total Bijection Bool Bool
boolNot = F (arr not)
            (arr not)

-- GHC infers the type
--
--   example :: F (Kleisli Identity)
--                (Kleisli NonEmpty)
--                Int
--                Bool
--
-- meaning we have a total surjection from Int to Bool, as witnessed by
--
--   image :: Int -> Bool
--   image = runIdentity . runKleisli (to example)
--
--   preimages :: Bool -> NonEmpty Int
--   preimages = runKleisli (from example)
-- 
example = boolNot <.> isPositive <.> plus 5
```

For a simple example of use, check out [CaesarCipher.hs](Examples/CaesarCipher.hs)
in which the Caesar Cipher is defined, for any group, in such a way that its
encode and decode functions are given simultaneously.

Constructing functions
======================

So we can build rich functions using a category-like interface; big deal.
But things get interesting when we mix in algebraic datatypes.
By giving types for sums and products, as we do in
[Data.Algebraic.Product](Data/Algebraic/Product.hs) and
[Data.Algebraic.Sum](Data/Algebraic/Sum.hs), we can construct rich functions
componentwise. That's to say, if you give a product of `F`s, then you have
an `F` on a corresponding product or sum:

```Haskell
-- GLBFold takes the greatest-lower-bound of 0 or more things.
productF :: (F f1 g1 s1 t1 :*: ... :*: F fn gn sn tn)
         -> F (GLBFold [f1,..,fn])
              (GLBFold [g1,..,gn])
              (s1 :*: ... :*: sn)
              (t1 :*: ... :*: tn)

sumF :: (F f1 g1 s1 t1 :*: ... :*: F fn gn sn tn)
     -> F (GLBFold [f1,..,fn])
          (GLBFold [g1,..,gn])
          (s1 :+: ... :+: sn)
          (t1 :+: ... :+: tn)
```

These are not the types as they appear in GHCi, since these functions are
implemented via type classes, but that's what they essentially are.

When interested in `F`s where the domain and codomain are not equally-sized
sums or products, we can turn to these functions:

```Haskell
-- There is a total bijection between any product, and that same product with
-- an () inserted anywhere into it. For instance, using normal Haskell tuple
-- notation, (String, Int) and (String, Int, ()) are clearly isomorphic.
introduceTerm :: Index index
              -> F Total
                   Bijection
                   product
                   (IntroduceTerm () product index)

-- Dually to introduceTerm, we can replace () with Void, which is the identity
-- for sums, and we obtain a total bijection from any sum to that same sum
-- with a Void thrown in.
introduceSummand :: Index index
                 -> F Total
                      Bijection
                      sum
                      (IntroduceSummand Void sum index)

-- We can also eliminate a () from any product.
-- The type doesn't show it, but this function will only work when
-- the component of the product at index is ().
eliminateTerm :: Index index
              -> F Total
                   Bijection
                   product
                   (EliminateTerm product index)

-- This is only possible when the summand at index is of type Void.
eliminateSummand :: Index index
                 -> F Total
                      Bijection
                      sum
                      (EliminateSummand sum index)
```

The fact that we must reach `()` or `Void` in order to shrink a product or sum,
respectively, is exactly what we expect. It forces an `F` from a bigger sum to
a smaller one to be partial (because a function from `t /= Void` to `Void`
must be partial), and an `F` from a bigger product to a smaller one to not be
injective.

See the [Tuple](Examples/Tuple.hs) example for elementary use of
`productF` and `eliminateTerm` to create tuple projections.



Invertible printers (parsers included)
======================================

Suppose we want to print a datatype. We'll need a function of type `t -> String`,
or some other string-like thing. Suppose we'd also like to be able to parse the
printed thing: we need something which is left-inverse to the printer.
Lessons learnt from exisiting parser libraries show us that a parser is not
`String -> t`, but `String -> (t, String)` or something similar, noting that
it's important to produce another string after parsing, to represent the
remaining, unparsed input.
So if we want an invertible printer, we'd better have something more like
`(t, String) -> String`, because when you flip this function around, you get
the type of a parser. But now we have trouble composing printers. We
have `printer2 <.> printer1` only when `printer2 :: String -> (u, String)`.
If we make the type symmetrical, things are much cleaner. So, we choose
`(s, String) -> (t, String)` for an invertible printer. Bring this into
the world of `F`, and we'll be working with

```Haskell
type PrinterPaser stream g h s t = F g h (s, stream) (t, stream)
```

Check out the [PrinterParser](Examples/PrinterParser.hs) example to see this
in action. It's actually pretty cool: when you define a printer/parser for a
sum type of two or more summands, the reversal becomes a `Function`, meaning
that when you parse it, you get 0 or more results, which is just what we want,
because the parsers for the summands may overlap! That's to say, if you
construct an ambiguous parser, it will produce all possible preimages under
the printer!
