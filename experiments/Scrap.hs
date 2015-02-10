-- scrap-your-boilerplate in terms of traversable functors
-- lesson: not possible in ghc 7.8; we need DeriveTraversable2,
-- DeriveTraversable3, etc.

{-# LANGUAGE DeriveTraversable, DeriveFunctor, DeriveFoldable,
             DeriveDataTypeable, RankNTypes #-}

import Data.Typeable
import Data.Foldable
import Data.Traversable

data C d = C [d]         deriving (Functor, Foldable, Traversable, Typeable)
data D n m u = D n m [u] deriving (Functor, Foldable, Traversable, Typeable)
data U e d = PU e | DU d deriving (Functor, Foldable, Traversable, Typeable)
data E p s = E p s       deriving (Functor, Foldable, Traversable, Typeable)
data P n a = P n a       deriving (Functor, Foldable, Traversable, Typeable)
data S f = S f           deriving (Functor, Foldable, Traversable, Typeable)

type Name = String
type Address = String
type Salary = S Float
type Person = P Name Address
type Employee = E Person Salary
type Manager = Employee
newtype Dept = Dept { unD :: D Name Manager SubUnit }
type SubUnit = U Employee Dept
type Company = C Dept

dept :: Name -> Manager -> [SubUnit] -> Dept
dept name manager subunits = Dept $ D name manager subunits

ralf, joost, marlow, blair :: Employee
ralf = E (P "Ralf" "Amsterdam") (S 8000)
joost = E (P "Joost" "Amsterdam") (S 1000)
marlow = E (P "Marlow" "Cambridge") (S 2000)
blair = E (P "Blair" "London") (S 100000)

genCom :: Company
genCom = C [dept "Research" ralf [PU joost, PU marlow],
            dept "Strategy" blair []]

-- ouch! need DeriveTraversable2, etc.
-- class (Traversable ..., Typeable ...) => Data ... where
--   gfoldl :: Applicative g => ...
--   gfoldl = traverseN

