{-# LANGUAGE GADTs #-}
module Data.Profunctor.Trace
  ( Trace(..)
  ) where

-- | Coend of profunctor from Hask -> Hask
data Trace f where
  Trace :: f a a -> Trace f
