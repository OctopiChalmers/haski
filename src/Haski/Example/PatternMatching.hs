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
        [ \ v -> (v `gtE` 3, T1 v)
        , \ v -> (val True, T2)
        ]

nats :: Haski (Stream Int)
nats = mdo
    n <- 0 `fby` (1 + n)
    return n

mainpm :: Stream Int -> Haski (Stream Int)
mainpm = node "mainpm" $ \ ns -> mdo
    -- numbers <- nats
    -- let altered = alter numbers
    alter ns


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