{-# LANGUAGE GADTs #-}
module Data.Profunctor.Composition 
  ( Procompose(..)
  , proidl
  , proidr
  , coproidl
  , coproidr
  ) where

import Data.Profunctor

data Procompose f g d c where
  Procompose :: f d a -> g a c -> Procompose f g d c 

instance (Profunctor f, Profunctor g) => Profunctor (Procompose f g) where
  lmap k (Procompose f g) = Procompose (lmap k f) g
  rmap k (Procompose f g) = Procompose f (rmap k g)

instance Profunctor g => Functor (Procompose f g a) where
  fmap k (Procompose f g) = Procompose f (rmap k g)

proidl :: Profunctor g => Procompose (->) g d c -> g d c 
proidl (Procompose f g) = lmap f g

proidr :: Profunctor f => Procompose f (->) d c -> f d c
proidr (Procompose f g) = rmap g f

coproidl :: g d c -> Procompose (->) g d c
coproidl = Procompose id

coproidr :: f d c -> Procompose f (->) d c
coproidr g = Procompose g id
