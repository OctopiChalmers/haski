{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RecursiveDo #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Haski.Example.Paper where

import Prelude hiding (Left)
import Text.PrettyPrint.HughesPJClass (Pretty,pPrint,text)

import Haski.Lang
import Haski.DCLabel.Core (principal)
import Haski.DCLabel.PrettyShow

import Debug.Trace

---------------
-- Section 2 --
---------------

data Action = Left | Entered
    deriving (Eq,Show,Enum,Bounded)

data Req  = Read | Write Action
    deriving (Eq, Show)

cache :: Stream Req -> Haski (Stream Action)
cache = {-node "cache" $ -}\ req -> mdo
   resp <- req `match` \case
        Read    -> state
        Write x -> val x
   state <- Left `fby` resp
   return resp

secCache :: LStream Req -> Haski (LStream Action)
secCache = node "secCache" $ \ req_l -> do
    resp <- unlabel req_l >>= cache
    l <- labelOf req_l
    label l resp

---------------
-- Section 5 --
---------------

data WindowOp = Skip | Open | Close
    deriving (Show,Eq,Bounded,Enum)

type Status = Maybe Action

halexa :: Stream Int -> LStream Status -> Haski (LStream WindowOp)
halexa = node "halexa" $ \temp stat_l -> do
    isHot <- letDef $ temp `gtE` 30
    toLabeled $ do
        stat <- unlabel stat_l
        -- ask server for the last known action
        pastAct  <- (stat `match` mkReq) >>= cache
        -- if `stat` has an update then use that, else use `pastAct`
        recentAct <- stat `match` (maybe pastAct val)
        -- compute decision based on `recentAct`
        dec <- recentAct `match` \case
            -- Octavius left, close the window!
            Left    -> val Close
            -- Octavius is home, open if its hot
            Entered -> ifte isHot (val Open) (val Skip)
        return dec
    where
        mkReq :: Status -> Stream Req
        mkReq Nothing  = val Read
        mkReq (Just x) = val (Write x)

halexaMain :: Haski (Stream WindowOp)
halexaMain = do
    rootLabel <- getLabel
    status_l  <- label rootLabel (val Nothing)
    (res,l)   <- runAs (halexa 15 status_l) (principal "Alexa")
    printL l
    return res

-----------------
-- Boilerplate --
-----------------

instance Bounded Req where
    minBound = Read
    maxBound = Write Entered

instance Enum Req where
    toEnum 0 = Read
    toEnum 1 = Write Left
    toEnum 2 = Write Entered
    fromEnum Read = 0
    fromEnum (Write Left) = 1
    fromEnum (Write Entered)  = 2

instance BEnum Req where
    type Size Req = 3
instance FinEnum Req where
instance Pretty Req where
    pPrint = text . show
instance LT Req where
    typeRepLT = userDefLT

instance BEnum Action where
    type Size Action = 2
instance FinEnum Action where
instance Pretty Action where
    pPrint = text . show
instance LT Action where
    typeRepLT = userDefLT

printL :: PrettyShow a => a -> Haski ()
printL l = trace (show $ "Label: " ++ prettyShow l) (return ())

printFL :: Haski ()
printFL = do
    fl <- getLabel
    trace (show $ "Floating label: " ++ prettyShow fl) (return ())


instance Bounded Status where
    minBound = Nothing
    maxBound = Just (maxBound)
instance Enum Status where
    toEnum 0 = Nothing
    toEnum x = Just $ toEnum (x - 1)
    fromEnum Nothing  = 0
    fromEnum (Just x) = 1 + (fromEnum x)

instance BEnum Status where
    type Size Status = 3
instance FinEnum Status where
instance {-# OVERLAPPING #-} Pretty Status where
    pPrint = text . show
instance LT Status where
    typeRepLT = userDefLT

instance BEnum WindowOp where
    type Size WindowOp = 3
instance FinEnum WindowOp where
instance {-# OVERLAPPING #-} Pretty WindowOp where
    pPrint = text . show
instance LT WindowOp where
    typeRepLT = userDefLT