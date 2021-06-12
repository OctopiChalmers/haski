{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Haski.Norm where

import Control.Monad.State
import GHC.TypeLits

import Haski.Core
import Haski.Enum
import Haski.Pass
import Haski.Type
import Haski.Util
import qualified Haski.Vec as V


-- normalization pass
data NormP

type Invalid (typ :: Symbol) (val :: Symbol)  = 'ShowType val
    :<>: 'Text " is not in normal form ("
    :<>: 'ShowType typ :<>: 'Text ")"

-- NormP enforces the predicate "NA" (from the paper) on expressions
type instance ArgVal NormP = ()
type instance ArgVar NormP = ()
type instance ArgWhn NormP = ()
type instance ArgAdd NormP = ()
type instance ArgMul NormP = ()
type instance ArgAbs NormP = ()
type instance ArgSig NormP = ()
type instance ArgNeg NormP = ()
type instance ArgGt  NormP = ()
type instance ArgFby NormP = TypeError (Invalid "NA" "Fby")
type instance ArgMrg NormP = TypeError (Invalid "NA" "Merge")

type instance ArgGtPoly NormP   = ()
type instance ArgEq NormP       = ()
type instance ArgNot NormP      = ()
type instance ArgIfte NormP     = ()
type instance ArgSym NormP      = ()
type instance ArgFieldExp NormP = ()
-- NOTE: Like with clocks, the normalization of CaseOfs is not argued to be
-- correct; if we need to define TypeErrors for some more types I would not
-- know.
type instance ArgCaseOf NormP   = ()

-- normal control expressions
data NCA p a where
    NExp :: NGExp p a ->  NCA p a
    NMrg :: (RecEnumerable n b)
        => ArgMrg p
        -> Var (BFin n b)
        -> V.Vec n (NCA p a)
        -> NCA p a

-- "Equations" are definitions in normal form
data EQ p where
    LetEq :: LT a => Var a -> NCA p a -> EQ p
    FbyEq :: LT a => ArgFby p -> Var a -> a -> NGExp p a -> EQ p
    AppEq :: LT a => Var a -> Name -> [Ex (NGExp p)] -> EQ p

-- node containing equations
data EQNode p where
    EQNode :: LT a
        => Name      -- ^ name
        -> [Ex Var]  -- ^ args
        -> [EQ p]    -- ^ body of eqs.
        -> NGExp p a -- ^ result (e.g., return e)
        -> EQNode p

data St p = MkSt { next :: Seed, subs :: [Sub p] }

type Norm p = State (St p)

instance Plant (St p) Seed where
    plant seed = modify $ \ st -> st {next = seed}

instance Plant (St p) [Sub p] where
    plant subs = modify $ \ st -> st {subs = subs}

instance Fresh (St p) where
    getSeed = next <$> get

data Sub p where
    SubFby  :: LT a
        => ArgFby p -> Var a -> a -> NGExp p a -> Sub p
    SubMrg  :: (LT a, RecEnumerable n b)
        => ArgMrg p -> Var a -> Var (BFin n b) -> V.Vec n (NCA p a) -> Sub p


subToEq :: Sub p -> EQ p
subToEq (SubFby ann x v e)
    = FbyEq ann x v e
subToEq (SubMrg ann x scrut branches)
    = LetEq x (NMrg ann scrut branches)

defToEq :: NGDef p -> EQ p
defToEq (Let x e)
    = LetEq x (NExp e)
defToEq (App x name args)
    = AppEq x name args

-- extend the accumulated substitution
extend :: Sub p -> Norm p ()
extend s = consTo subs s

type NGExp p  = GExp (p,NormP)
type NGDef p  = GDef (p,NormP)
type NGNode p = GNode (p,NormP)

pattern NGVal ann x     = GVal (ann,()) x
pattern NGVar ann x     = GVar (ann,()) x
pattern NGWhn ann e tup = GWhn (ann,()) e tup
pattern NGAdd ann e1 e2 = GAdd (ann,()) e1 e2
pattern NGMul ann e1 e2 = GMul (ann,()) e1 e2
pattern NGAbs ann e     = GAbs (ann,()) e
pattern NGSig ann e     = GSig (ann,()) e
pattern NGNeg ann e     = GNeg (ann,()) e
pattern NGGt :: () => (a ~ Bool) => ArgGt p -> NGExp p Int -> NGExp p Int -> NGExp p a
pattern NGGt ann e1 e2 = GGt (ann,()) e1 e2

pattern NGGtPoly :: () => (LT a, Num a, b ~ Bool)
    => ArgGtPoly p -> NGExp p a -> NGExp p a -> NGExp p b
pattern NGGtPoly ann e1 e2   = GGtPoly (ann,()) e1 e2
pattern NGEq :: () => (LT a, Eq a, b ~ Bool)
    => ArgEq p -> NGExp p a -> NGExp p a -> NGExp p b
pattern NGEq ann e1 e2   = GEq (ann,()) e1 e2
pattern NGNot :: () => (a ~ Bool) => ArgNot p -> NGExp p Bool -> NGExp p a
pattern NGNot ann e1         = GNot (ann,()) e1
pattern NGIfte ann b e1 e2   = GIfte (ann,()) b e1 e2
pattern NGSym ann sid        = GSym (ann, ()) sid
pattern NGFieldExp ann tag e = GFieldExp (ann, ()) tag e
pattern NGCaseOf ann scrut branches = GCaseOf (ann, ()) scrut branches

-- normalize control expressions
normCA :: forall p q a . (AllEq p q) => GExp p a -> Norm p (NCA p a)
-- a nested merge, no substitution is generated
normCA (GMrg ann scrut branches) = do
    -- normalize branches
    branches' <- sequenceA (normCA <$> branches)
    -- rebuild merge expression
    return (NMrg ann scrut branches')
-- non-merge expression, so normalize simply and lift to NCA
normCA e = NExp <$> normE e

-- normalize an expression
normE :: (AllEq p q) => GExp p a -> Norm p (NGExp p a)
normE (GVal ann v) = return (NGVal ann v)
normE (GVar ann x) = return (NGVar ann x)
normE (GFby ann v e) = do
    e' <- normE e
    x <- fresh
    extend $ SubFby ann x v e'
    return (NGVar ann x)
normE (GWhn ann e (x,c)) = do
    e' <- normE e
    return (NGWhn ann e' (x,c))
-- a top-level merge, substitution is generated
normE (GMrg ann scrut branches) = do
    -- normalize branches
    branches' <- sequenceA (normCA <$> branches)
    -- generate substitution for this (top-level) merge
    x <- fresh
    extend $ SubMrg ann x scrut branches'
    -- return a variable in-place of merge
    return (NGVar ann x)
normE (GAdd ann e1 e2) = do
    e1' <- normE e1
    e2' <- normE e2 -- eww, e2' normalizes in the filth of e1'
    return (NGAdd ann e1' e2')
normE (GMul ann e1 e2) = do
    e1' <- normE e1
    e2' <- normE e2 -- eww, e2' normalizes in the filth of e1'
    return (NGMul ann e1' e2')
normE (GAbs ann e) = do
    e' <- normE e
    return (NGAbs ann e')
normE (GSig ann e) = do
    e' <- normE e
    return (NGSig ann e')
normE (GNeg ann e) = do
    e' <- normE e
    return (NGNeg ann e')
normE (GGt ann e1 e2) = do
    e1' <- normE e1
    e2' <- normE e2 -- eww, e2' normalizes in the filth of e1'
    return (NGGt ann e1' e2')

normE (GGtPoly ann e1 e2)   = NGGtPoly ann <$> normE e1 <*> normE e2
normE (GEq ann e1 e2)       = NGEq ann <$> normE e1 <*> normE e2
normE (GNot ann e)          = NGNot ann <$> normE e
normE (GIfte ann b e1 e2)   = NGIfte ann <$> normE b <*> normE e1 <*> normE e2
normE (GSym ann sid)        = return (NGSym ann sid)
normE (GFieldExp ann tag e) = NGFieldExp ann tag <$> normE e
normE (GCaseOf ann scrut branches) = do
    scrut' <- normScrut scrut
    branches' <- mapM normBranch branches
    return $ NGCaseOf ann scrut' branches'
  where
    normScrut :: (AllEq p q) => Scrut p a -> Norm p (Scrut (p, NormP) a)
    normScrut (Scrut e sid) = flip Scrut sid <$> normE e

    normBranch :: (AllEq p q) => Branch p b -> Norm p (Branch (p, NormP) b)
    normBranch (Branch scrut branches) =
        Branch <$> normE scrut <*> normE branches


-- normalize a definition (monadic result)
normD :: (AllEq p q) => GDef p -> Norm p (NGDef p)
normD (Let x e) = do
    e' <- normE e
    return (Let x e')
normD (App x nodeName args) = do
    args' <- sequenceA (exMapM normE <$> args)
    return (App x nodeName args')

-- normalize a node
normN :: (AllEq p q) => GNode p -> Norm p (NGNode p)
normN (GNode name args defs res) = do
    defs' <- sequenceA (normD <$> defs)
    res'  <- normE res
    return (GNode name args defs' res')

-- normalize defs to equations
normDefs :: (AllEq p q) => [GDef p] -> Norm p [EQ p]
normDefs defs = map defToEq <$> mapM normD defs

-- normalize a node to produce an equation-node
normNode :: (AllEq p q) => GNode p -> Seed -> (EQNode p, Seed)
normNode node seed = (mkEqNode node' subs, seed)
    where
    (node', MkSt seed' subs) = runState (normN node) (MkSt seed [])
    -- pack a node along with its residual substitution
    mkEqNode :: forall p q . (AllEq p q) => NGNode p -> [Sub p] -> EQNode p
    mkEqNode (GNode name args defs res) subs = EQNode name args eqs res
        where eqs = (map defToEq defs ++ map subToEq subs)
