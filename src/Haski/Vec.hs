{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE GADTs #-}

-- needed for `++.`
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Haski.Vec where

import Prelude hiding (zipWith, (++), unzip)
import GHC.TypeLits

-- | Non-empty vector
data Vec (n :: Nat) a where
    Last   :: a -> Vec 1 a
    Cons   :: a -> Vec n a -> Vec (n + 1) a

-- Convert vector to list
toList :: Vec n a -> [ a ]
toList (Last x) = [ x ]
toList (Cons x v) = x : toList v

-- Append vectors
(++) :: Vec n a -> Vec m a -> Vec (n + m) a
v ++ (Last x) = Cons x v
v ++ (Cons x u) = Cons x (v ++ u)

-- First element of a vector
head :: Vec n a -> a
head (Last x)   = x
head (Cons x _) = x

-- Apply
ap :: Vec n (a -> b) -> Vec n a -> Vec n b
ap f x = zipWith ($) f x

zipWith :: (a -> b -> c) -> Vec n a -> Vec n b -> Vec n c
zipWith f (Last x) (Last y) = Last (f x y)
zipWith f (Cons x xs) (Cons y ys) = Cons (f x y) (zipWith f xs ys)

zipWithM :: Applicative m => (a -> b -> m c) -> Vec n a -> Vec n b -> m (Vec n c)
zipWithM f x y = sequenceA (zipWith f x y)

unzipWith :: (c -> (a,b)) -> Vec n c -> (Vec n a, Vec n b)
unzipWith f (Last x) = let (p,q) = f x
    in (Last p, Last q)
unzipWith f (Cons x xs) = let (p,q) = f x ; (ps,qs) = unzipWith f xs
    in (Cons p ps, Cons q qs)

unzip :: Vec n (a, b) -> (Vec n a, Vec n b)
unzip = unzipWith id

instance Foldable (Vec n) where
    foldr f b (Last x) = f x b
    foldr f b (Cons x xs) = f x (foldr f b xs)

instance Traversable (Vec n) where
    traverse f (Last x)    = Last <$> (f x)
    traverse f (Cons x xs) = Cons <$> (f x) <*> traverse f xs

    -- gives definition for sequenceA

instance Functor (Vec n) where
    fmap f (Last x) = Last (f x)
    fmap f (Cons x v) = Cons (f x) (fmap f v)
