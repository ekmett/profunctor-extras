{-# LANGUAGE GADTs, FlexibleInstances, UndecidableInstances #-}
module Data.Profunctor.Collage 
  ( Collage(..)
  ) where

import Data.Semigroupoid
import Data.Semigroupoid.Coproduct (L(..), R(..))
import Data.Profunctor

-- | The cograph of a profunctor
data Collage k b a where
  L :: (b -> b') -> Collage k (L b) (L b')
  R :: (a -> a') -> Collage k (R a) (R a')
  C :: k b a     -> Collage k (L b) (R a)
  
instance Profunctor k => Semigroupoid (Collage k) where
  L f `o` L g = L (f . g)
  R f `o` R g = R (f . g) 
  R f `o` C g = C (rmap f g)
  C f `o` L g = C (lmap g f)
