{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeFamilies #-}

module Haski.Example.Cache where

import Haski.Lang
import Text.PrettyPrint.HughesPJClass (Pretty,pPrint,text)

data Req  = Read | Write Bool
    deriving (Eq, Show)

data Resp = Ok | Val Bool
    deriving (Eq, Show)

cache :: Stream Req -> Haski (Stream Resp)
cache = node "cache" $ \req -> mdo

    -- update state (a Bool stream)
    st <- req `match` \case
        Read    -> st'
        Write x -> val x
    st' <- False `fby` st

    -- prepare response (a Resp stream)
    resp <- req `match` \case
        Read    -> mapE Val st
        Write _ -> val Ok
    return resp

-- invokes `cache` by altenating requests
-- between writing `True` and reading it
cacheMain :: Haski (Stream Resp)
cacheMain = mdo
    req <- Write True `fby` aux
    aux <- Read `fby` req
    res <- cache req
    return res

-----------------
-- Boilerplate --
-----------------

instance Bounded Req where
    minBound = Read
    maxBound = Write True

instance Enum Req where
    toEnum 0 = Read
    toEnum 1 = Write False
    toEnum 2 = Write True
    fromEnum Read          = 0
    fromEnum (Write False) = 1
    fromEnum (Write True)  = 2

instance Bounded Resp where
    minBound = Ok
    maxBound = Val True

instance Enum Resp where
    toEnum 0 = Ok
    toEnum 1 = Val False
    toEnum 2 = Val True
    fromEnum Ok          = 0
    fromEnum (Val False) = 1
    fromEnum (Val True)  = 2

instance BEnum Req where
    type Size Req = 3

instance BEnum Resp where
    type Size Resp = 3

instance FinEnum Req where
instance FinEnum Resp where

instance Pretty Req where
    pPrint = text . show
instance Pretty Resp where
    pPrint = text . show

instance LT Req where
    typeRepLT = userDefLT
instance LT Resp where
    typeRepLT = userDefLT
