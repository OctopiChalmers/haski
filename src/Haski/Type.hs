{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}

-- needed for the pattern synonyms
{-# OPTIONS_GHC -fplugin GHC.TypeLits.Normalise #-}

module Haski.Type (
    module Haski.Type
    , eqT, gcast
    , KnownNat
    , (:~:)(..)
) where

import Haski.Enum

import Data.Int (Int8)
import Data.Typeable

import Control.Applicative ((<|>))
import GHC.TypeLits (KnownNat)

import Text.PrettyPrint.HughesPJClass (Pretty(..),int)

data TypeRepLT a where
    TUnit :: TypeRepLT ()
    TBool :: TypeRepLT Bool
    TInt8 :: TypeRepLT Int8
    TInt  :: TypeRepLT Int
    TBFin :: TypeRepLT (BFin n a)
    TUDef :: FinEnumPack a => TypeRepLT a

-- user defined type
userDefLT :: FinEnumPack a => TypeRepLT a
userDefLT = TUDef

-- NOTE: `Typeable a` is not strictly needed since typeRepLT already
--  gives us a type-representation, but it's convenient since
--  it implements much of the boilerplate for casting,
--  equality checking, etc.

class (Pretty a, Typeable a, Eq a) => LT a where
    -- | `typeRepLT` ensures that the universe
    -- of supported types is closed
    typeRepLT :: TypeRepLT a

instance LT () where
    typeRepLT = TUnit

instance LT Bool where
    typeRepLT = TBool

instance Pretty Int8 => LT Int8 where
    typeRepLT = TInt8

instance LT Int where
    typeRepLT = TInt

-- `KnownNat n` is needed for deriving `Typeable (C n)`
instance (KnownNat n, LT a) => LT (BFin n a) where
    typeRepLT = TBFin

eqT' :: LT a => f a -> g a -> Bool
eqT' x y = typeRep x == typeRep y

eq :: forall a b f . (Typeable a, Typeable b, Eq (f a))
    => f a -> f b -> Bool
eq x y = case eqT @a @b of
    Just Refl -> x == y
    Nothing   -> False

instance Pretty Int8 where
    pPrint = int . fromIntegral

instance {-# OVERLAPPING #-} Pretty (BFin n a) where
    pPrint v = int (enumVal v)

-------------------------------
-- Finite Enum type-constraint
-------------------------------

-- FinEnum is an (invisible) indirection to FinEnumPack.
-- The only purpose of this class is to hide the details
-- incredibly noisy details of FinEnumPack.
class FinEnumPack a => FinEnum a where

-- The *actual* constraint used internally
-- for enumeration and to transform BEnum to BFin
type FinEnumPack a = (BEnum a
    , BEnum (BFin (Size a) a)
    , KnownNat (Size a)
    , Enumerable (Size a) (BFin (Size a) a))

instance FinEnum Bool where
instance FinEnum Int8 where
