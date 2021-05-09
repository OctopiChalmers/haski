{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}

module Haski.Example.Simple where

import Data.Int
import Haski.Lang
import Haski.TH
import Text.PrettyPrint.HughesPJClass (Pretty,pPrint,text)

-- [0, 1, 2, 3,...]
nats :: Haski (Stream Int)
nats = mdo
    n <- 0 `fby` (1 + n)
    return n

-- [0, 1, 1, 2, 3,...]
fib :: Haski (Stream Int)
fib = mdo
    x <- 0 `fby` y
    y <- 1 `fby` (x + y)
    return x

-- [True, False, True, False,...]
alt :: Haski (Stream Bool)
alt = mdo
    tru <- True `fby` fls
    fls <- False `fby` tru
    return tru

-- [0,2,4,8,10,...]
evens :: Haski (Stream Int)
evens = mdo
    ns <- nats
    bs <- alt
    es <- letDef $ ns `when` (bs , True)
    return es

-- count number of ticks (True values of `tick`)
-- between two tops (True values of `top`)
counting :: Stream Bool -> Stream Bool -> Haski (Stream Int)
counting = node "counting" $ \ tick top -> mdo
    o' <- 0 `fby` o
    o <- tick `match` \case
            True -> v
            False -> o' + v
    v <- top `match` \case
            True -> 1
            False -> 0
    return o

-- invocation of `counting`
countingCall :: Haski (Stream Int)
countingCall = do
    let tick = val True
    top <- alt
    counting tick top


-- Testing simple CaseOf-style pattern matching stuff

alter :: Stream Int -> Haski (Stream Int)
alter s = s `caseof` \case
    T1 n b -> n + 1
    T2     -> s

type HELLO = Stream Int

data T = T1 HELLO (Stream Bool) | T2
$(mkConstructors ''T)
instance Partition Int T where
    partition =
        [ \ v -> (v `gtE` 3, _T1 (v * 999) (v `gtE` 100))
        , \ v -> (val True, _T2)
        ]

data WrapInt = WrapInt (Stream Int)
$(mkConstructors ''WrapInt)
instance Partition Bool WrapInt where
    partition =
        [ \ v -> (v, _WrapInt 100)
        , \ v -> (ifte v (val False) (val True), _WrapInt 99)
        ]

pm1 :: Stream Int -> Stream Bool -> Haski (Stream Int)
pm1 = node "pmnode" $ \ ns bs -> mdo
    x <- ns `caseof` \case
        T1 n b -> b
        T2     -> val False
    y <- x `caseof` \case
        WrapInt n -> n
    return y

pm1call :: Haski (Stream Int)
pm1call = do
    ns <- nats
    bs <- alt
    pm1 ns bs
