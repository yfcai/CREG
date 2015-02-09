-- paramorphisms are definable as anamorphisms
-- composed with catamorphisms with respect to
-- a composed functor.

{-# LANGUAGE RankNTypes, ScopedTypeVariables #-}

import Prelude hiding (Functor)

type Functor f = forall a b. (a -> b) -> f a -> f b

newtype Fix f = Roll { unroll :: f (Fix f) }

cata :: Functor f -> (f a -> a) -> Fix f -> a
cata fmap algebra = algebra . fmap (cata fmap algebra) . unroll

ana :: Functor f -> (a -> f a) -> a -> Fix f
ana fmap coalgebra = Roll . fmap (ana fmap coalgebra) . coalgebra

sndF :: Functor ((,) a)
sndF f (x, y) = (x, f y)


-- lol: can't define functor composition without newtype
newtype Compose f g a = Compose { decompose :: (f (g a)) }
(∘) :: Functor f -> Functor g -> Functor (Compose f g)
(fmap ∘ gmap) f = Compose . fmap (gmap f) . decompose


para :: Functor f -> (f (Fix f, a) -> a) -> Fix f -> a
para fmap psi =
  let
    pairingF = fmap ∘ sndF
    pairingCoalgebra = Compose . fmap (\t -> (t, t)) . unroll
    composedAlgebra = psi . decompose
  in
    cata pairingF composedAlgebra . ana pairingF pairingCoalgebra
