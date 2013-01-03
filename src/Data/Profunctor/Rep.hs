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
    Representable(..), tabulated
  -- * Corepresentable Profunctors
  , Corepresentable(..), cotabulated
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
class (Functor (Rep p), Profunctor p) => Representable p where
  type Rep p :: * -> *
  tabulate :: (d -> Rep p c) -> p d c
  rep :: p d c -> d -> Rep p c

instance Representable (->) where
  type Rep (->) = Identity
  tabulate f = runIdentity . f
  rep f = Identity . f

instance (Monad m, Functor m) => Representable (Kleisli m) where
  type Rep (Kleisli m) = m
  tabulate = Kleisli
  rep = runKleisli

instance Functor f => Representable (UpStar f) where
  type Rep (UpStar f) = f
  tabulate = UpStar
  rep = runUpStar

-- | The composition of two representable profunctors is representable by the composition of their representations.
instance (Representable p, Representable q) => Representable (Procompose p q) where
  type Rep (Procompose p q) = Compose (Rep p) (Rep q)
  tabulate f = Procompose (tabulate (getCompose . f)) (tabulate id)
  rep (Procompose f g) d = Compose $ rep g <$> rep f d

-- | 'tabulate' and 'rep' form two halves of an isomorphism.
--
-- This can be used with the combinators from the @lens@ package.
--
-- @'tabulated' :: 'Representable' p => 'Iso'' (d -> 'Rep' p c) (p d c)@
tabulated :: (Profunctor r, Functor f, Representable p, Representable q)
          => r (p d c) (f (q d' c'))
          -> r (d -> Rep p c) (f (d' -> Rep q c'))
tabulated = dimap tabulate (fmap rep)

-- * Corepresentable Profunctors

-- | A 'Profunctor' @p@ is corepresentable if there exists a 'Functor' @f@ such that
-- @p d c@ is isomorphic to @f d -> c@.
class (Functor (Corep p), Profunctor p) => Corepresentable p where
  type Corep p :: * -> *
  cotabulate :: (Corep p d -> c) -> p d c
  corep :: p d c -> Corep p d -> c

instance Corepresentable (->) where
  type Corep (->) = Identity
  cotabulate f = f . Identity
  corep f (Identity d) = f d

instance Functor w => Corepresentable (Cokleisli w) where
  type Corep (Cokleisli w) = w
  cotabulate = Cokleisli
  corep = runCokleisli

instance Corepresentable Tagged where
  type Corep Tagged = Proxy
  cotabulate f = Tagged (f Proxy)
  corep (Tagged a) _ = a

instance Functor f => Corepresentable (DownStar f) where
  type Corep (DownStar f) = f
  cotabulate = DownStar
  corep = runDownStar

instance (Corepresentable p, Corepresentable q) => Corepresentable (Procompose p q) where
  type Corep (Procompose p q) = Compose (Corep q) (Corep p)
  cotabulate f = Procompose (cotabulate id) (cotabulate (f . Compose))
  corep (Procompose f g) (Compose d) = corep g $ corep f <$> d

-- | 'cotabulate' and 'corep' form two halves of an isomorphism.
--
-- This can be used with the combinators from the @lens@ package.
--
-- @'tabulated' :: 'Corep' f p => 'Iso'' (f d -> c) (p d c)@
cotabulated :: (Profunctor r, Functor h, Corepresentable p, Corepresentable q)
          => r (p d c) (h (q d' c'))
          -> r (Corep p d -> c) (h (Corep q d' -> c'))
cotabulated = dimap cotabulate (fmap corep)
