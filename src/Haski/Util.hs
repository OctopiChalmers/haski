{-# LANGUAGE GADTs #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE UndecidableInstances #-}
module Haski.Util where

import Control.Monad.State.Lazy (StateT, get, execState, modify)
import Control.Monad (replicateM)

import Haski.Type

---------
-- Named
---------

type Name = String

-- Name things, even dolphins do!
class Named a where
    getName :: a -> Name

------
-- Ex
------

-- Consider types `Var a` and Exp a`,
-- where Var,Exp :: * -> *
-- The type `Ex` (exists) allows us to say `Ex Var` and `Ex Exp`
-- when we don't care about `a` (but only that there exists one)
data Ex f where
    Ex :: LT a => f a -> Ex f

exMap :: (forall a . f a -> g a) -> Ex f -> Ex g
exMap f (Ex x) = Ex (f x)

exMapM :: Monad m => (forall a . f a -> m (g a)) -> Ex f -> m (Ex g)
exMapM f (Ex x) = Ex <$> (f x)

-- eliminate an existential quantification
extract :: (forall a . LT a => f a -> b) -> Ex f -> b
extract f (Ex x) = f x

instance (forall a . LT a => Eq (f a)) => Eq (Ex f) where
    (Ex x) == (Ex y) = maybe False (==y) (gcast x)

instance (forall a . LT a => Ord (f a)) => Ord (Ex f) where
    (Ex x) <= (Ex y) = maybe False (<=y) (gcast x)

---------
-- Plant
---------

-- Plant is a `put` specialized to fields in the state
class Plant s a where
    plant :: (Monad m) => a -> StateT s m ()

-- cons a list element in state
consTo :: (Monad m, Plant s [a]) => (s -> [a]) -> a -> StateT s m ()
consTo r x = do
    xs <- r <$> get
    plant (x : xs)

type Seed = Int

nextSeed :: Int -> Int
nextSeed = (+1)

class (Plant s Seed) => Fresh s where
    getSeed  :: (Monad m) => StateT s m Seed

freshName :: (Fresh s, Monad m) => String -> StateT s m (String)
freshName pre = do
    seed <- getSeed
    plant (nextSeed seed)
    return $ pre ++ (letters !! seed)
    where
    letters    = [1..] >>= flip replicateM ['a'..'z']
