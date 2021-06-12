{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Haski.Pass where

import GHC.Exts (Constraint)


type family ArgVal      p :: *
type family ArgVar      p :: *
type family ArgFby      p :: *
type family ArgWhn      p :: *
type family ArgMrg      p :: *
type family ArgAdd      p :: *
type family ArgMul      p :: *
type family ArgAbs      p :: *
type family ArgSig      p :: *
type family ArgNeg      p :: *
type family ArgGt       p :: *
type family ArgGtPoly   p :: *
type family ArgEq       p :: *
type family ArgNot      p :: *
type family ArgIfte     p :: *
type family ArgCaseOf   p :: *
type family ArgSym      p :: *
type family ArgFieldExp p :: *

type AllEq p a =
    ((ArgVal p) ~ a, (ArgVar p) ~ a, (ArgFby p) ~ a
    , (ArgWhn p) ~ a, (ArgMrg p) ~ a, (ArgAdd p) ~ a
    , (ArgMul p) ~ a, (ArgAbs p) ~ a, (ArgSig p)  ~ a
    , (ArgNeg p) ~ a, (ArgGt p) ~ a
    , (ArgGtPoly p) ~ a
    , (ArgEq p) ~ a
    , (ArgNot p) ~ a
    , (ArgIfte p) ~ a
    , (ArgCaseOf p) ~ a
    , (ArgSym p) ~ a
    , (ArgFieldExp p) ~ a
    )

type ForallArg p (c :: * -> Constraint) =
    (c (ArgVal p), c (ArgVar p), c (ArgFby p)
    , c (ArgWhn p), c (ArgMrg p), c (ArgAdd p)
    , c (ArgMul p), c (ArgAbs p), c (ArgSig p)
    , c (ArgNeg p), c (ArgGt p)
    , c (ArgGtPoly p)
    , c (ArgEq p)
    , c (ArgNot p)
    , c (ArgIfte p)
    , c (ArgCaseOf p)
    , c (ArgSym p)
    , c (ArgFieldExp p)
    )

data RawP

type instance ArgVal      RawP = ()
type instance ArgVar      RawP = ()
type instance ArgFby      RawP = ()
type instance ArgWhn      RawP = ()
type instance ArgMrg      RawP = ()
type instance ArgAdd      RawP = ()
type instance ArgMul      RawP = ()
type instance ArgAbs      RawP = ()
type instance ArgSig      RawP = ()
type instance ArgNeg      RawP = ()
type instance ArgGt       RawP = ()
type instance ArgGtPoly   RawP = ()
type instance ArgEq       RawP = ()
type instance ArgNot      RawP = ()
type instance ArgIfte     RawP = ()
type instance ArgCaseOf   RawP = ()
type instance ArgSym      RawP = ()
type instance ArgFieldExp RawP = ()

type instance ArgVal (a,b)      = (ArgVal a, ArgVal b)
type instance ArgVar (a,b)      = (ArgVar a, ArgVar b)
type instance ArgFby (a,b)      = (ArgFby a, ArgFby b)
type instance ArgWhn (a,b)      = (ArgWhn a, ArgWhn b)
type instance ArgMrg (a,b)      = (ArgMrg a, ArgMrg b)
type instance ArgAdd (a,b)      = (ArgAdd a, ArgAdd b)
type instance ArgMul (a,b)      = (ArgMul a, ArgMul b)
type instance ArgAbs (a,b)      = (ArgAbs a, ArgAbs b)
type instance ArgSig (a,b)      = (ArgSig a, ArgSig b)
type instance ArgNeg (a,b)      = (ArgNeg a, ArgNeg b)
type instance ArgGt  (a,b)      = (ArgGt a, ArgGt b)
type instance ArgGtPoly  (a,b)  = (ArgGtPoly a, ArgGtPoly b)
type instance ArgEq  (a,b)      = (ArgEq a, ArgEq b)
type instance ArgNot (a,b)      = (ArgNot a, ArgNot b)
type instance ArgIfte (a,b)     = (ArgIfte a, ArgIfte b)
type instance ArgCaseOf (a,b)   = (ArgCaseOf a , ArgCaseOf b)
type instance ArgSym (a,b)      = (ArgSym a , ArgSym b)
type instance ArgFieldExp (a,b) = (ArgSym a , ArgSym b)
