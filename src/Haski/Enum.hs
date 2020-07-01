{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ConstraintKinds #-}

-- needed for the pattern synonyms
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Haski.Enum (
    module Haski.Enum
)
where

import Haski.Fin
import GHC.TypeLits
import Data.Int (Int8)
import qualified Haski.Vec as V

class MinBoundInt a where
    minBoundInt :: Int

data MinBoundIntC a where
    MinBoundIntC :: (MinBoundInt a) => MinBoundIntC a

type BFin n a = Fin n (MinBoundIntC a)

enumVal :: forall n a . BFin n a -> Int
enumVal (Stop MinBoundIntC) = minBoundInt @a
enumVal (Next x)            = enumVal x + 1

-----------------------------
-- API for enumerating values
-----------------------------

-- enumerate the first n values of a type
class Enumerable (n :: Nat) a where
    enumerate :: V.Vec n a

---------------------------------------------------
-- Safe implementation of enumeration API for BFin
---------------------------------------------------

instance {-# OVERLAPPING #-} MinBoundInt a => Enumerable 1 (BFin 1 a) where
    enumerate = V.Last (Stop MinBoundIntC)

instance {-# OVERLAPPING #-} (Enumerable n (BFin n a), n1 ~ (n + 1))
    => Enumerable n1 (BFin n1 a) where
    enumerate = V.Cons (Next (V.head ts)) (fmap raise1 ts)
        where ts = enumerate @n @(BFin n a)

----------
-- BEnum
----------

-- Statically Bound Enum
class (Bounded a, Enum a) => BEnum a where
    type Size a :: Nat
    -- Invariant:
    -- natVal (Size a) == length [minBound @a .. maxBound @a]

instance BEnum () where
    type Size ()   = 1

instance BEnum Bool where
    type Size Bool = 2

instance BEnum Int8 where
    type Size Int8 = 256

------------------------------------
-- BEnum a => Enumerable (Size a) a
------------------------------------

instance {-# OVERLAPPING #-} (BEnum a) => Enumerable 1 a where
    enumerate = V.Last minBound

instance (Enumerable n a, f n1 ~ f (n + 1), BEnum a) => Enumerable n1 a where
    enumerate = V.Cons (succ $ V.head ts) ts
        where ts = enumerate @n @a

--------------------------------
-- BEnum a => BEnum (BFin n a)
--------------------------------

-- BEnum a => MinBoundInt a
instance BEnum a => MinBoundInt a where
    minBoundInt = fromEnum (minBound @a)

-- MinBoundInt a => Bounded (BFin n a)

instance {-# OVERLAPPING #-} MinBoundInt a => Bounded (BFin 1 a) where
    minBound = Stop MinBoundIntC
    maxBound = Stop MinBoundIntC

instance (Bounded (BFin n a), f n1 ~ f (n + 1)) => Bounded (BFin n1 a) where
    minBound = raise1 (minBound @(BFin n a))
    maxBound = Next (maxBound @(BFin n a))

-- MinBoundInt a => Enum (BFin n a)

instance {-# OVERLAPPING #-} (MinBoundInt a) => Enum (BFin 1 a) where
    fromEnum (Stop _) = 0

    toEnum 0          = Stop MinBoundIntC
    toEnum x          = error $ "toEnum underflow: " ++ show x

instance (Enum (BFin n a), f n1 ~ f (n + 1)) => Enum (BFin n1 a) where
    fromEnum (Stop _) = 0
    fromEnum (Next x) = (fromEnum @(BFin n a) x) + 1

    toEnum 0 = raise1 (toEnum @(BFin n a) 0)
    toEnum n = Next (toEnum @(BFin n a) (n - 1))

-- BEnum (BFin n a)

instance (Bounded (BFin n a), Enum (BFin n a)) => BEnum (BFin n a) where
    type Size (BFin n a) = n

--------------
-- Corollaries
--------------

bEnumIso :: forall a b . (BEnum a, BEnum b, Size a ~ Size b)
    => a -> b
bEnumIso x = toEnum @b (x' - min_a + min_b)
    where
        min_a    = fromEnum (minBound @a)
        min_b    = fromEnum (minBound @b)
        x'       = fromEnum x

toBFin :: forall a . (BEnum a, BEnum (BFin (Size a) a))
    => a -> BFin (Size a) a
toBFin = bEnumIso @a @(BFin (Size a) a)

fromBFin :: forall a . (BEnum a, BEnum (BFin (Size a) a))
    => BFin (Size a) a -> a
fromBFin = bEnumIso @(BFin (Size a) a) @a


-- Boilerplate

instance Show (MinBoundIntC a) where
    show MinBoundIntC = "MinBoundIntC"

instance Eq (MinBoundIntC a) where
    MinBoundIntC == MinBoundIntC = True
