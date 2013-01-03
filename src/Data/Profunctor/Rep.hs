{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
-----------------------------------------------------------------------------
-- |
-- Module      :  Data.Profunctor.Rep
-- Copyright   :  (C) 2011-2012 Edward Kmett,
-- License     :  BSD-style (see the file LICENSE)
--
-- Maintainer  :  Edward Kmett <ekmett@gmail.com>
-- Stability   :  provisional
-- Portability :  MPTCs
--
----------------------------------------------------------------------------
module Data.Profunctor.Rep
  (
  -- * Representable Profunctors
    Rep(..), tabulated
  -- * Corepresentable Profunctors
  , Corep(..), cotabulated
  ) where

import Control.Arrow
import Control.Comonad
import Data.Functor.Compose
import Data.Functor.Identity
import Data.Profunctor
import Data.Profunctor.Composition
import Data.Proxy
import Data.Tagged

-- * Representable Profunctors

-- | A 'Profunctor' @p@ is representable if there exists a 'Functor' @f@ such that
-- @p d c@ is isomorphic to @d -> f c@.
class (Functor f, Profunctor p) => Rep f p where
  tabulate :: (d -> f c) -> p d c
  rep :: p d c -> d -> f c

instance Rep Identity (->) where
  tabulate f = runIdentity . f
  rep f = Identity . f

instance (Monad m, Functor m) => Rep m (Kleisli m) where
  tabulate = Kleisli
  rep = runKleisli

instance Functor f => Rep f (UpStar f) where
  tabulate = UpStar
  rep = runUpStar

-- | The composition of two representable profunctors is representable by the composition of their representations.
instance (Rep f p, Rep g q) => Rep (Compose f g) (Procompose p q) where
  tabulate f = Procompose (tabulate (getCompose . f)) (tabulate id)
  rep (Procompose f g) d = Compose $ rep g <$> rep f d

-- | 'tabulate' and 'rep' form two halves of an isomorphism.
--
-- This can be used with the combinators from the @lens@ package.
--
-- @'tabulated' :: 'Rep' f p => 'Iso'' (d -> f c) (p d c)@
tabulated :: (Profunctor r, Functor h, Rep f p, Rep g q)
          => r (p d c) (h (q d' c'))
          -> r (d -> f c) (h (d' -> g c'))
tabulated = dimap tabulate (fmap rep)

-- * Corepresentable Profunctors

-- | A 'Profunctor' @p@ is representable if there exists a 'Functor' @f@ such that
-- @p d c@ is isomorphic to @d -> f c@.
class (Functor f, Profunctor p) => Corep f p where
  cotabulate :: (f d -> c) -> p d c
  corep :: p d c -> f d -> c

instance Corep Identity (->) where
  cotabulate f = f . Identity
  corep f (Identity d) = f d

instance Functor w => Corep w (Cokleisli w) where
  cotabulate = Cokleisli
  corep = runCokleisli

instance Corep Proxy Tagged where
  cotabulate f = Tagged (f Proxy)
  corep (Tagged a) _ = a

instance Functor f => Corep f (DownStar f) where
  cotabulate = DownStar
  corep = runDownStar

instance (Corep f p, Corep g q) => Corep (Compose g f) (Procompose p q) where
  cotabulate f = Procompose (cotabulate id) (cotabulate (f . Compose))
  corep (Procompose f g) (Compose d) = corep g $ corep f <$> d

-- | 'cotabulate' and 'corep' form two halves of an isomorphism.
--
-- This can be used with the combinators from the @lens@ package.
--
-- @'tabulated' :: 'Corep' f p => 'Iso'' (f d -> c) (p d c)@
cotabulated :: (Profunctor r, Functor h, Corep f p, Corep g q)
          => r (p d c) (h (q d' c'))
          -> r (f d -> c) (h (g d' -> c'))
cotabulated = dimap cotabulate (fmap corep)
