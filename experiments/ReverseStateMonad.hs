{-# LANGUAGE
  AllowAmbiguousTypes,
  FlexibleContexts,
  UndecidableInstances,
  DeriveFunctor,
  DeriveFoldable,
  DeriveTraversable #-}

-- investigating the reverse state monad:
-- https://lukepalmer.wordpress.com/2008/08/10/mindfuck-the-reverse-state-monad/

import Control.Applicative
import Data.Traversable
import Data.Foldable(Foldable)

newtype RState s a = RState { runRState :: s -> (a,s) }
evalRState s f = fst (runRState f s)

instance Monad (RState s) where
    return x = RState $ (,) x
    RState sf >>= f = RState $ \s ->
        let (a,s'') = sf s'
            (b,s') = runRState (f a) s
        in (b,s'')

instance Functor (RState s) where
  fmap f mx = do
    x <- mx
    return $ f x

instance Applicative (RState s) where
  pure = return
  mf <*> mx = do
    f <- mf
    x <- mx
    return (f x)

get = RState $ \s -> (s,s)
modify f = RState $ \s -> ((),f s)
put = modify . const

-- cumulativeSums [1,2,3,4,5] = [0,1,3,6,10,15]
cumulativeSums = scanl (+) 0

computeFibs = evalRState (repeat 1) $ do
    fibs <- get
    -- here the state is what we want: the fibonacci numbers
    modify cumulativeSums
    -- now the state is the difference sequence of
    -- fibs, [1,0,1,1,2,3,5,8,13,...], because the
    -- cumulativeSums of that sequence is fibs.  Notice
    -- that this sequence is the same as 1:fibs, so
    -- just put that to get here.
    put (1:fibs)
    -- And here the state is empty (or whatever else
    -- we want it to be, because we just overwrite it on
    -- the previous line -- but we defined it to be
    -- empty on the evalRState line)
    return fibs

newtype Fix f = Roll { unroll :: f (Fix f) }

instance Show (f (Fix f)) => Show (Fix f) where
  show t = "(" ++ (show $ unroll t) ++ ")"

data TreeF a t
  = Leaf a
  | Branch t t
  deriving (Functor, Foldable, Traversable, Show)

type Tree a = Fix (TreeF a)

foldM :: (Traversable t, Applicative m, Monad m) =>
         (t a -> m a) -> Fix t -> m a
foldM algM x = traverse (foldM algM) (unroll x) >>= algM

-- different state monads
class StateMonad state where
  readState  :: state s s
  writeState :: s -> state s ()
  evalState :: state s a -> s -> a


newtype State s a = State { runState :: s -> (a, s) }

instance StateMonad State where
  readState  = State (\s -> (s, s))
  writeState s  = State (\s' -> ((), s))
  evalState m s = fst (runState m s)

instance StateMonad RState where
  readState = get
  writeState = put
  evalState m s = fst (runRState m s)

instance Monad (State a) where
  return x = State $ ((,) x)
  ma >>= f = State $ \s -> let (a, s') = runState ma s in runState (f a) s'

instance Functor (State a) where
  fmap f mx = do
    x <- mx
    return (f x)

instance Applicative (State a) where
  pure = return
  mf <*> mx = do
    f <- mf
    x <- mx
    return (f x)

uniqM :: (StateMonad m, Monad (m Int), Applicative (m Int)) =>
         m Int Int -> -- dummy param to help typeclass resolution
         Tree a -> m Int (Tree Int)
uniqM _ = foldM $ \t -> case t of
  Leaf x -> do
    n <- readState
    writeState (n + 1)
    return $ Roll $ Leaf n

  Branch l r -> return $ Roll $ Branch l r

-- selector for forward state monad
state :: State Int Int
state = State undefined

-- selector for backward state monad
rstate :: RState Int Int
rstate = RState undefined

uniq :: (StateMonad m, Monad (m Int), Applicative (m Int)) =>
        m Int Int ->
        Tree a -> Tree Int

uniq tag t = evalState (uniqM tag t) 0

branch x y = Roll $ Branch x y
leaf = Roll . Leaf

tree :: Tree String
tree =
  branch
    (branch (leaf "hello") (leaf "world"))
    (branch
      (branch (leaf "goodbye") (leaf "cruel"))
      (leaf "world"))

forwardTree :: Tree Int
forwardTree = uniq state tree
-- (Branch (Branch (Leaf 0) (Leaf 1)) (Branch (Branch (Leaf 2) (Leaf 3)) (Leaf 4)))

backwardTree :: Tree Int
backwardTree = uniq rstate tree
-- (Branch (Branch (Leaf *** Exception: <<loop>>
