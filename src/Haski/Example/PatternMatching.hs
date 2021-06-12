{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE TemplateHaskell       #-}

{- | Testing simple CaseOf-style pattern matching stuff -}

module Haski.Example.PatternMatching where

import Haski.Example.Simple
import Haski.Lang
import Haski.TH

-- * Pattern matching using identity instances

-- Makes use the 'Partition Int8 Int8' instance to get behavior similar to
-- that of 'match'.
lit :: Stream Int8 -> Haski (Stream Int8)
lit = node "lit" $ \ns -> mdo
    caseof ns $ \case
        0 -> 0
        1 -> 99
        n | odd n  -> val n
          | even n -> val (-n)

litcall :: Haski (Stream Int8)
litcall = mdo
    ns <- letDef 1
    lit ns

-- * Pattern matching on Double

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

-- * More complex types

type ErrorCode = Stream Int
type Celsius   = Stream Double
data Temperature
    = Hot
    | Great Celsius
    | Cold
    | Error ErrorCode
$(mkConstructors ''Temperature)

data Moisture
    = Dry
    | Wet
$(mkConstructors ''Moisture)

instance Partition Double Temperature where
    partition =
        [ \ v -> (v >. 999, _Error 127)
        , \ v -> (v >. 38,  _Hot)
        , \ v -> (v >. 5,   _Great (v * 10))
        , \ _ -> (val True, _Error 1)
        ]

instance Partition Int Moisture where
    partition =
        [ \ v -> (v >. 20,  _Wet)
        , \ _ -> (val True, _Dry)
        ]

needsWatering :: Stream Double -> Stream Int -> Haski (Stream Bool)
needsWatering = node "needsWatering" $ \ temp moist -> mdo
    isDry <- moist `caseof` \case
        Dry -> val True
        Wet -> val False
    isHot <- temp `caseof` \case
        Hot        -> val True
        Great _    -> val False
        Cold       -> val False
        Error code -> code >. 126
    return $ iftePrim isDry  -- 'iftePrim' is potentially unsafe!
                (val True)
                isHot

needsWateringCall :: Haski (Stream Bool)
needsWateringCall = do
    moistStream <- nats
    let tempStream = val 26
    needsWatering tempStream moistStream
