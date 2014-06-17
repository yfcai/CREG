-- Use of applicative functors as in:
-- Bringert, Ranta.
-- A pattern for almost compositional functions.

-- unfortunately this is not possible in Haskell due to "Typeable"
-- being bad.

-- point is, it's possible to write gfoldl if an applicative
-- functor instance is given as argument.

-- very powerful combination: gfoldl with applicative!
-- can do gmapQ in a type-safe manner.
-- count free variables? no problem! first map all leaves to
-- sets of 1 or 0, then fold with binders being one case
-- and gfoldl collecting sets in other cases.


import Control.Exception
import Unsafe.Coerce




class Applicative f where
  pure :: a -> f a
  (<*>) :: f (a -> b) -> f a -> f b

class Data a where
  -- default gfoldl: pure.
  gfoldl :: Applicative w => a -> w a
  gfoldl = pure

data Tree = Leaf Int | Branch [Tree] deriving (Show)

instance Data Tree where
  gfoldl (Leaf n) = pure (Leaf n) -- leaf has no children... (debatable)
  gfoldl (Branch ts) = pure Branch <*> pure ts


-- application 1: increase salary
-- Salary takes any type to itself
newtype Salary a = Salary { unsalary :: a }


instance Applicative Salary where
  -- this does not work.
  pure x = case unsafeCoerce x :: Tree of
    Leaf n -> Salary (unsafeCoerce (Leaf (n + div n 10)))
    x -> Salary (unsafeCoerce x)
  (Salary f) <*> (Salary x) = Salary (f x)

