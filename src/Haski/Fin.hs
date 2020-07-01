{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveDataTypeable #-}

-- needed for `raise`
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Haski.Fin where

import GHC.TypeLits
import Data.Proxy (Proxy(..))
import Data.Typeable

-- Finite (homogenous sum) type of a fixed size
-- Fin 1 a = a
-- Fin 2 a = a + a
-- Fin n a = a + ... + a (n times)
-- Similar to the Fin type in Agda
data Fin (n :: Nat) a where
    Stop   :: a -> Fin (n + 1) a
    Next   :: Fin n a -> Fin (n + 1) a
    deriving (Typeable)

-- Raise size of the Fin-type by 1
raise1 :: Fin n a -> Fin (n + 1) a
raise1 (Stop x) = Stop x
raise1 (Next s) = Next (raise1 s)

raise :: forall n m a . Fin n a -> Fin (n + m) a
raise (Stop x) = Stop x
raise (Next s) = Next (raise s)

-- | Unique integer assigned to an inhabitant
valRep :: Fin n a -> Int
valRep (Stop _) = 0
valRep (Next s) = valRep s + 1

instance Show a => Show (Fin n a) where
    show (Stop x) = "Stop" ++ " " ++show x
    show (Next x) = "Next" ++ "(" ++ show x ++ ")"

instance Eq a => Eq (Fin n a) where
    (Stop x) == (Stop y) = x == y
    (Next m) == (Next n) = m == n
    _        == _        = False

instance Functor (Fin n) where
    fmap f (Stop x) = Stop (f x)
    fmap f (Next v) = Next (fmap f v)
