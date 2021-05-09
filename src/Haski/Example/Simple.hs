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
counting :: Stream Bool -> Stream Bool -> Stream Int -> Haski (Stream Int)
counting = node "counting" $ \ tick top nums -> mdo
    o' <- 0 `fby` o
    o <- tick `match` \case
            True -> v
            False -> o' + v
    v <- top `match` \case
            True -> 1
            False -> 0

    caseof (nums + o) $ \case
        T1 n -> n + n + n + 1
        T2   -> v
    -- return o

-- invocation of `counting`
countingCall :: Haski (Stream Int)
countingCall = do
    let tick = val True
    top <- alt
    nums <- nats
    counting tick top nums


-- Testing simple CaseOf-style pattern matching stuff

alter :: Stream Int -> Haski (Stream Int)
alter s = s `caseof` \case
    T1 n -> n + 1
    T2   -> s

data T = T1 (Stream Int) | T2
$(mkConstructors ''T)
instance Partition Int T where
    partition =
        [ \ v -> (v `gtE` 3, _T1 (v * 999))
        , \ v -> (val True, _T2)
        ]

pmnode :: Stream Int -> Haski (Stream Int)
pmnode = node "pmnode" $ \ ns -> mdo
    pure ns

testProg = nats >>= pmnode
