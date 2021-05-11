{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE TemplateHaskell       #-}

{- | Testing simple CaseOf-style pattern matching stuff -}

module Haski.Example.PatternMatching where

import Haski.Example.Simple
import Haski.Lang
import Haski.TH

-- * Pattern matching on Double

type Temp = Stream Double
data HasFever
    = Burning
    | Barely
    | Healthy
$(mkConstructors ''HasFever)

instance Partition Double HasFever where
    partition =
        [ \ d -> (d >. 41,   _Burning)
        , \ d -> (d >. 37.5, _Barely)
        , \ _ -> (val True,  _Healthy)
        ]

-- | Take a stream of doubles as input and return a different value depending
-- on the input.
feverScore :: Stream Double -> Haski (Stream Double)
feverScore = node "feverScore" $ \ ds -> mdo
    score <- ds `caseof` \case
        Burning -> ds * 3000  -- Big bonus for being close to death
        Barely  -> ds
        Healthy -> 0
    return score

-- | Entry point
feverScoreCall :: Haski (Stream Double)
feverScoreCall = do
    -- Start counting from 33
    ds <- dfrom 33
    feverScore ds

-- | Start counting in steps of 1 from some number.
dfrom :: (Num a, LT a) => a -> Haski (Stream a)
dfrom start = mdo
    d <- start `fby` (1 + d)
    return d
