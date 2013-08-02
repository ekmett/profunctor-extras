{-# LANGUAGE CPP #-}
{-# LANGUAGE Rank2Types #-}
#if defined(__GLASGOW_HASKELL__) && __GLASGOW_HASKELL__ >= 702
{-# LANGUAGE Trustworthy #-}
#endif
-----------------------------------------------------------------------------
-- |
-- Copyright   :  (C) 2013 Edward Kmett and Dan Doel
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  Rank2Types
--
----------------------------------------------------------------------------
module Data.Profunctor.Rift
  ( Rift(..)
  ) where

import Data.Profunctor.Unsafe

-- | This represents the right Kan lift of a 'Profunctor' q along a 'Profunctor' p.
newtype Rift p q a b = Rift { runRift :: forall x. p x a -> q x b }

instance (Profunctor p, Profunctor q) => Profunctor (Rift p q) where
  dimap ca bd f = Rift (rmap bd . runRift f . rmap ca)
  {-# INLINE dimap #-}
  lmap ca f = Rift (runRift f . rmap ca)
  {-# INLINE lmap #-}
  rmap bd f = Rift (rmap bd . runRift f)
  {-# INLINE rmap #-}
  bd #. f = Rift (\p -> bd #. runRift f p)
  {-# INLINE (#.) #-}
  f .# ca = Rift (\p -> runRift f (ca #. p))
  {-# INLINE (.#) #-}

instance Profunctor q => Functor (Rift p q a) where
  fmap bd f = Rift (rmap bd . runRift f)
  {-# INLINE fmap #-}
