{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecursiveDo           #-}

module Haski.Example.PatternMatching where

import Haski.Lang


-- Testing pattern matching stuff

alter :: Stream Int -> Haski (Stream Int)
alter s = s `caseof` \case
    T1 n -> n + 1
    T2   -> s

data T = T1 (Stream Int) | T2
instance Partition Int T where
    partition =
        [ \ v -> (v `gtE` 3, pure $ T1 v)
        , \ v -> (val True, pure T2)
        ]

nats :: Haski (Stream Int)
nats = mdo
    n <- 0 `fby` (1 + n)
    return n

pmnode :: Stream Int -> Haski (Stream Int)
pmnode = node "pmnode" $ \ ns -> mdo
    -- numbers <- nats
    -- let altered = alter numbers
    alter ns

testProg = nats >>= pmnode

-- counting :: Stream Bool -> Stream Bool -> Haski (Stream Int)
-- counting = node "counting" $ \ tick top -> mdo
--     o' <- 0 `fby` o
--     o <- tick `match` \case
--             True -> v
--             False -> o' + v
--     v <- top `match` \case
--             True -> 1
--             False -> 0
--     return o