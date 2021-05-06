-- TODO: Clean up stuff from the CaseOf addition (imports etc.)
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ConstraintKinds #-}

module Haski.Core where

import Prelude hiding ((<>))
import GHC.TypeLits
import qualified Data.Map as M
import Data.Coerce (coerce)
import Data.Constraint (Dict(..))
import Data.Typeable (Typeable)

import Control.Monad (mapM, guard, zipWithM_)
import Control.Monad.State.Lazy (StateT, get, execState, modify)

import Haski.Fin
import Haski.Enum
import qualified Haski.Vec as V
import Haski.Type
import Haski.Util
import Haski.Pass

-- Variables (annotated)
newtype Var a = MkVar (Name, Maybe String)

-- Match expression to handle an enum replue
type GMatch p n a = V.Vec n (GExp p a)

theTrick :: forall a b . (FinEnum a) => (a -> b) -> V.Vec (Size a) b
theTrick f = (f . fromBFin) <$> (enumerate @(Size a) @(BFin (Size a) a))

type RecEnumerable n a = (LT a, Enumerable n (BFin n a), KnownNat n)

data GExp p a where
    -- Values and Variables
    GVal     :: LT a
        => ArgVal p -> a -> GExp p a
    GVar     :: LT a
        => ArgVar p -> Var a -> GExp p a

    -- Stream combinators
    GFby     :: (LT a)
        => ArgFby p -> a -> GExp p a -> GExp p a
    GWhn    :: (LT a, RecEnumerable n b)
        => ArgWhn p -> GExp p a -> (Var (BFin n b), BFin n b) -> GExp p a
    GMrg   :: (LT a, RecEnumerable n b)
        => ArgMrg p -> Var (BFin n b) -> GMatch p n a -> GExp p a

    -- Primitive operators
    GAdd     :: (LT a)
        => ArgAdd p -> GExp p a -> GExp p a -> GExp p a
    GMul     :: (LT a)
        => ArgMul p -> GExp p a -> GExp p a -> GExp p a
    GAbs     :: (LT a)
        => ArgAbs p -> GExp p a -> GExp p a
    GSig     :: (LT a)
        => ArgSig p -> GExp p a -> GExp p a
    GNeg     :: (LT a)
        => ArgNeg p -> GExp p a -> GExp p a
    GGt     :: ()
        => ArgGt p -> GExp p Int -> GExp p Int -> GExp p Bool

    -- Pattern matching
    GCaseOf :: (LT a, LT b)
        => ArgCaseOf p -> Scrut p a -> [Branch p b] -> GExp p b
    -- GSym :: LT a => ArgSym p -> ScrutId -> GExp p a

-- Scrutinee of a pattern match
data Scrut p a = LT a => Scrut (GExp p a) ScrutId
type ScrutId = String

-- Branch of a pattern match (predicate on scrutinee for selecting branch
-- + body of branch, which is an expression)
data Branch p b = LT b => Branch (GExp p Bool) (GExp p b)

data GDef p where
    Let :: LT a => Var a -> GExp p a -> GDef p
    App :: LT a => Var a -> Name -> [Ex (GExp p)] -> GDef p

type Node = GNode RawP

data GNode p where
    GNode :: LT a => Name -> [Ex Var] -> [GDef p] -> GExp p a -> GNode p

type Stream = GExp RawP
type Def = GDef RawP
type Match n a = GMatch RawP n a

pattern Val   x     = GVal () x
pattern Var   x     = GVar () x
pattern Fby   x  e  = GFby () x e
pattern When  e  t  = GWhn () e t
pattern Merge x  m  = GMrg () x m
pattern Add   e1 e2 = GAdd () e1 e2
pattern Mul   e1 e2 = GMul () e1 e2
pattern Abs   e     = GAbs () e
pattern Sig   e     = GSig () e
pattern Neg   e     = GNeg () e
pattern Gt :: (ArgGt p ~ ()) => (a ~ Bool)
    => GExp p Int -> GExp p Int -> GExp p a
pattern Gt e1 e2    = GGt () e1 e2
pattern CaseOf scrut branches = GCaseOf () scrut branches
-- pattern Sym scrutId = GSym () scrutId


-- Treat (number) expressions as numbers
instance (LT a, Num a) => Num (Stream a) where
    c1 + c2       = Add c1 c2
    c1 * c2       = Mul c1 c2
    abs c         = Abs c
    signum c      = Sig c
    fromInteger c = Val $ fromInteger c
    negate c      = Neg c

instance Named (GNode p) where
    getName (GNode name _ _ _) = name

instance Named (Var a) where
    getName (MkVar p) = fst p

instance Named (Ex Var) where
    getName x = extract getName x

mapAnn :: (AllEq p p', AllEq q q')
    => (p' -> q') -> GExp p a -> GExp q a
mapAnn f (GVal p x)    = GVal (f p) x
mapAnn f (GVar p x)    = GVar (f p) x
mapAnn f (GFby p x e)  = GFby (f p) x (mapAnn f e)
mapAnn f (GWhn p e xc) = GWhn (f p) (mapAnn f e) xc
mapAnn f (GMrg p x m)  = GMrg (f p) x (fmap (mapAnn f) m)
mapAnn f (GAdd p e e') = GAdd (f p) (mapAnn f e) (mapAnn f e')
mapAnn f (GMul p e e') = GMul (f p) (mapAnn f e) (mapAnn f e')
mapAnn f (GAbs p e )   = GAbs (f p) (mapAnn f e)
mapAnn f (GSig p e )   = GSig (f p) (mapAnn f e)
mapAnn f (GNeg p e )   = GNeg (f p) (mapAnn f e)
mapAnn f (GGt p e e')  = GGt (f p) (mapAnn f e) (mapAnn f e')
mapAnn f (GCaseOf p scrut branches) =
    GCaseOf (f p) (annScrut f scrut) (map (annBranch f) branches)
  where
    annScrut :: (AllEq p0 p0', AllEq q0 q0')
        => (p0' -> q0') -> Scrut p0 a -> Scrut q0 a
    annScrut f (Scrut e sid) = Scrut (mapAnn f e) sid

    annBranch :: (AllEq p0 p0', AllEq q0 q0')
        => (p0' -> q0') -> Branch p0 b -> Branch q0 b
    annBranch f (Branch predE bodyE) = Branch (mapAnn f predE) (mapAnn f bodyE)
-- mapAnn f (GSym p sid) = GSym (f p) sid

mapSndAnn :: (AllEq q q', AllEq r r')
    => (q' -> r') -> GExp (p,q) a -> GExp (p,r) a
mapSndAnn f (GVal (p,q) x)    = GVal (p, f q) x
mapSndAnn f (GVar (p,q) x)    = GVar (p, f q) x
mapSndAnn f (GFby (p,q) x e)  = GFby (p, f q) x (mapSndAnn f e)
mapSndAnn f (GWhn (p,q) e xc) = GWhn (p, f q) (mapSndAnn f e) xc
mapSndAnn f (GMrg (p,q) x m)  = GMrg (p, f q) x (fmap (mapSndAnn f) m)
mapSndAnn f (GAdd (p,q) e e') = GAdd (p, f q) (mapSndAnn f e) (mapSndAnn f e')
mapSndAnn f (GMul (p,q) e e') = GMul (p, f q) (mapSndAnn f e) (mapSndAnn f e')
mapSndAnn f (GAbs (p,q) e )   = GAbs (p, f q) (mapSndAnn f e)
mapSndAnn f (GSig (p,q) e )   = GSig (p, f q) (mapSndAnn f e)
mapSndAnn f (GNeg (p,q) e )   = GNeg (p, f q) (mapSndAnn f e)
mapSndAnn f (GGt (p,q) e e')  = GGt (p, f q) (mapSndAnn f e) (mapSndAnn f e')
mapSndAnn f (GCaseOf (p,q) scrut branches) =
    GCaseOf (p, f q) (sndAnnScrut f scrut) (map (sndAnnBranch f) branches)
  where
    sndAnnScrut :: (AllEq q0 q0', AllEq r0 r0')
        => (q0' -> r0') -> Scrut (p0, q0) a -> Scrut (p0, r0) a
    sndAnnScrut f (Scrut e sid) = Scrut (mapSndAnn f e) sid

    sndAnnBranch :: (AllEq q0 q0', AllEq r0 r0')
        => (q0' -> r0') -> Branch (p0, q0) a -> Branch (p0, r0) a
    sndAnnBranch f (Branch predE bodyE) =
        Branch (mapSndAnn f predE) (mapSndAnn f bodyE)
-- mapSndAnn f (GSym (p, q) sid) = GSym (p, f q) sid

mapDef :: (forall a . GExp p a -> GExp q a)
    -> GDef p -> GDef q
mapDef f (Let x e)
    = Let x (f e)
mapDef f (App x node args)
    = App x node (map (exMap f) args)

mapNode :: (forall a . GExp p a -> GExp q a)
    -> GNode p
    -> GNode q
mapNode f (GNode name args defs res) =
    GNode name args (map (mapDef f) defs) (f res)

getAnn :: (AllEq p q)
    => GExp p a -> q
getAnn (GVal p x)    = p
getAnn (GVar p x)    = p
getAnn (GFby p x e)  = p
getAnn (GWhn p e xc) = p
getAnn (GMrg p x m)  = p
getAnn (GAdd p e e') = p
getAnn (GMul p e e') = p
getAnn (GAbs p e)    = p
getAnn (GSig p e)    = p
getAnn (GNeg p e)    = p
getAnn (GGt p e e')  = p
getAnn (GCaseOf p _predE _bodyE) = p
-- getAnn (GSym p _) = p

-- seems like a rather expensive operation, use sparingly!
-- the things we do for type-safety.. tsk tsk.
unpack :: GExp (p,q) a -> (GExp p a, GExp q a)
unpack (GVal (p,q) x)   = (GVal p x, GVal q x)
unpack (GVar (p,q) x)   = (GVar p x, GVar q x)
unpack (GFby (p,q) x e) = let (e1,e2) = unpack e
    in (GFby p x e1, GFby q x e2)
unpack (GWhn (p,q) e xc) = let (e1,e2) = unpack e
    in (GWhn p e1 xc, GWhn q e2 xc)
unpack (GMrg (p,q) x m)  = let (m1,m2) = V.unzip (fmap unpack m)
    in (GMrg p x m1, GMrg q x m2)
unpack (GAdd (p,q) e e') = let
    (e1, e2)   = unpack e
    (e1', e2') = unpack e'
    in (GAdd p e1 e1', GAdd q e2 e2')
unpack (GMul (p,q) e e') = let
    (e1, e2)   = unpack e
    (e1', e2') = unpack e'
    in (GMul p e1 e1', GMul q e2 e2')
unpack (GAbs (p,q) e)   = let (e1,e2) = unpack e
    in (GAbs p e1, GAbs q e2)
unpack (GSig (p,q) e)   = let (e1,e2) = unpack e
    in (GSig p e1, GSig q e2)
unpack (GNeg (p,q) e)   = let (e1,e2) = unpack e
    in (GNeg p e1, GNeg q e2)
unpack (GGt (p,q) e e') = let
    (e1, e2)   = unpack e
    (e1', e2') = unpack e'
    in (GGt p e1 e1', GGt q e2 e2')
unpack (GCaseOf (p, q) scrut branches) =
    let (scrut1, scrut2)       = unpackScrut scrut
        (branches1, branches2) = unzip $ map unpackBranch branches
    in (GCaseOf p scrut1 branches1, GCaseOf q scrut2 branches2)
  where
    unpackScrut :: Scrut (p, q) a -> (Scrut p a, Scrut q a)
    unpackScrut (Scrut e sid) =
        let (e1, e2) = unpack e
        in (Scrut e1 sid, Scrut e2 sid)

    unpackBranch :: Branch (p, q) b -> (Branch p b, Branch q b)
    unpackBranch (Branch predE bodyE) =
        let (predE1, predE2) = unpack predE
            (bodyE1, bodyE2) = unpack bodyE
        in (Branch predE1 bodyE1, Branch predE2 bodyE2)
-- unpack (GSym (p, q) sid) = (GSym p sid, GSym q sid)

fresh :: (Fresh s, Monad m) => StateT s m (Var a)
fresh = do
    name <- freshName ""
    return $ MkVar (name,Nothing)

cast :: forall a p . FinEnum a => Var a -> Var (BFin (Size a) a)
cast = coerce

getLTDict :: GExp p a -> Dict (LT a)
getLTDict (GVal _ _)      = Dict
getLTDict (GVar _ _)      = Dict
getLTDict (GFby _ _ _)    = Dict
getLTDict (GWhn _ e _)    = getLTDict e
getLTDict (GMrg _ _ bs)   = getLTDict (V.head bs)
getLTDict (GAdd _ e _)    = getLTDict e
getLTDict (GMul _ e _)    = getLTDict e
getLTDict (GSig _ e)      = getLTDict e
getLTDict (GNeg _ e)      = getLTDict e
getLTDict (GAbs _ e)      = getLTDict e
getLTDict (GGt _ _ _)     = Dict @(LT Bool)
getLTDict (GCaseOf _ _ _) = Dict
-- getLTDict (GSym _ _) = Dict
