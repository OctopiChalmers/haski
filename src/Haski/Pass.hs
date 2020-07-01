{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
module Haski.Pass where

import Haski.Util
import GHC.Exts (Constraint)

type family ArgVal p :: *
type family ArgVar p :: *
type family ArgFby p :: *
type family ArgWhn p :: *
type family ArgMrg p :: *
type family ArgAdd p :: *
type family ArgMul p :: *
type family ArgAbs p :: *
type family ArgSig p :: *
type family ArgNeg p :: *
type family ArgGt  p :: *

type AllEq p a =
    ((ArgVal p) ~ a, (ArgVar p) ~ a, (ArgFby p) ~ a
    , (ArgWhn p) ~ a, (ArgMrg p) ~ a, (ArgAdd p) ~ a
    , (ArgMul p) ~ a, (ArgAbs p) ~ a, (ArgSig p)  ~ a
    , (ArgNeg p) ~ a, (ArgGt p) ~ a
    )

type ForallArg p (c :: * -> Constraint) =
    (c (ArgVal p), c (ArgVar p), c (ArgFby p)
    , c (ArgWhn p), c (ArgMrg p), c (ArgAdd p)
    , c (ArgMul p), c (ArgAbs p), c (ArgSig p)
    , c (ArgNeg p), c (ArgGt p)
    )

data RawP

type instance ArgVal RawP = ()
type instance ArgVar RawP = ()
type instance ArgFby RawP = ()
type instance ArgWhn RawP = ()
type instance ArgMrg RawP = ()
type instance ArgAdd RawP = ()
type instance ArgMul RawP = ()
type instance ArgAbs RawP = ()
type instance ArgSig RawP = ()
type instance ArgNeg RawP = ()
type instance ArgGt  RawP = ()

type instance ArgVal (a,b) = (ArgVal a, ArgVal b)
type instance ArgVar (a,b) = (ArgVar a, ArgVar b)
type instance ArgFby (a,b) = (ArgFby a, ArgFby b)
type instance ArgWhn (a,b) = (ArgWhn a, ArgWhn b)
type instance ArgMrg (a,b) = (ArgMrg a, ArgMrg b)
type instance ArgAdd (a,b) = (ArgAdd a, ArgAdd b)
type instance ArgMul (a,b) = (ArgMul a, ArgMul b)
type instance ArgAbs (a,b) = (ArgAbs a, ArgAbs b)
type instance ArgSig (a,b) = (ArgSig a, ArgSig b)
type instance ArgNeg (a,b) = (ArgNeg a, ArgNeg b)
type instance ArgGt  (a,b) = (ArgGt a , ArgGt b)
