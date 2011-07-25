{-# LANGUAGE GADTs #-}
module Data.Profunctor.Composition 
  ( Compose(..)
  ) where

import Data.Profunctor

data Compose f g d c where
  Compose :: f d a -> g a c -> Compose f g d c 

instance (Profunctor f, Profunctor g) => Profunctor (Compose f g) where
  lmap k (Compose f g) = Compose (lmap k f) g
  rmap k (Compose f g) = Compose f (rmap k g)

instance Profunctor g => Functor (Compose f g a) where
  fmap k (Compose f g) = Compose f (rmap k g)
