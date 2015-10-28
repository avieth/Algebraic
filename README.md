Algebraic
=========

The goal of this experiment is to explore ways to construct functions
which are richer than the typical Haskell functions (of type `(->)`). In
particular, functions which are known to be bijective, or injective, or
surjective, or total, or partial, etc.

The foundation is this type, from [Data.Algebraic.Function](Data/Algebraic/Function.hs)

```Haskell
newtype F g h s t = F {
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

This ordering is expressed by the `ArrowHomomorphism` class and its instances,
and exploited by the function

```Haskell
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
```

By using `fcompose` as a replacement for the typical categorical composition
`(.)`, we allow GHC to infer the types of our functions.

```Haskell
plus :: Int -> F Total Bijection Int Int
plus i = F (arr ((+) i))
           (arr (\x -> x - i))

isPositive :: F Total Surjection Int Bool
isPositive = F (arr (\x -> x > 0))
               (Kleisli $ \b -> if b
                   then (1 :| [2..])
                   else negate (0 :| [1..])
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
example = boolNot `fcompose` isPositive `fcompose` plus 5
```
