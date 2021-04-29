{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Haski.Example.PatternMatching where

import Haski.Lang


-- Testing pattern matching stuff

ex :: Stream Int -> Stream Int
ex s = s `caseof` \case
    T1 n -> n + 1
    T2   -> s

data T = T1 (Stream Int) | T2
instance Partition Int T where
    partition =
        [ \ v -> (v `gtE` 0, T1 v)
        , \ v -> (val True, T2)
        ]
