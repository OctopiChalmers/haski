{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Haski.OBC where

import Haski.Core (Var,RecEnumerable)
import qualified Haski.Core as Core
import Haski.Norm
import Haski.Schedule (CNGExp, CNCA, CEQ, CEQNode, getClock,)

import Haski.Util
import Haski.Type
import qualified Haski.Vec as V
import Haski.Enum
import Haski.Fin
import Haski.Clock (Clock(..),ClockP)

import Data.Typeable (eqT)
import Data.Coerce (coerce)
import Data.Foldable (foldrM)
import qualified Data.Set as S

import Control.Monad.Reader hiding (join)
import Control.Monad.State.Lazy (State, StateT, get, runState, execState, modify)

newtype Field a = Field {toTup :: (Var a,a)}

data Obj = Obj {
    objName :: Name,    -- | Name of the instance
    objType :: Name     -- | Name of class
    }

-- | Class (or object "template") definition
data Class p where
    Class :: Name
        -> [Ex Field]   -- | Memory initialization
        -> [Obj]        -- | Instances
        -> [Stmt p]     -- | Reset statement
        -> Step p       -- | Step method
        -> Class p

-- | The "step" method
data Step p where
    Step :: LT a
        => [Ex Var]    -- | Arguments
        -> Exp p a      -- | Result
        -> [Stmt p]     -- | Body
        -> Step p

data Stmt p where
    Let     :: LT a => Var a -> Exp p a -> Stmt p
    Ass     :: Var a -> Exp p a -> Stmt p
    Skip    :: Stmt p
    Seq     :: Stmt p -> Stmt p -> Stmt p
    Case    :: (RecEnumerable n b)
        => Exp p (BFin n b) -- | Scrutinee
        -> V.Vec n (Stmt p)
        -> Stmt p
    CallReset   :: Obj -> Stmt p
    CallStep    :: LT a
        => Var a        -- | variable bound with result
        -> Obj          -- | object instance
        -> [Ex (Exp p)] -- | arguments
        -> Stmt p

data Exp p a where
    -- "simple" variable
    Var :: Var a -> Exp p a        -- "simple" variable
    -- reference variable (`Ref x` represents "store(x)")
    Ref :: Var a -> Exp p a
    Val :: LT a => a -> Exp p a
    Add :: Exp p a -> Exp p a -> Exp p a
    Mul :: Exp p a -> Exp p a -> Exp p a
    Sig :: Exp p a -> Exp p a
    Neg :: Exp p a -> Exp p a
    Abs :: Exp p a -> Exp p a
    Gt  :: Exp p Int -> Exp p Int -> Exp p Bool

deriving instance Eq (Var a)
deriving instance Eq (Exp p a)
deriving instance Ord (Var a)

instance Named Obj where
    getName = objName

instance Named (Class p) where
    getName (Class n _ _ _ _) = n

ifExp :: forall n p b . (RecEnumerable n b)
    => Exp p (BFin n b) -> BFin n b -> Stmt p -> Stmt p
ifExp e c s = Case e (fmap genBranch $ enumerate @n @(BFin n b))
    where
    genBranch c' = if c == c' then s else Skip

control :: Clock -> Stmt p -> Stmt p
control Base        s = s
control (On ck c x) s = control ck (ifExp (Var x) c s)

join :: Stmt p -> Stmt p -> Stmt p
join s1@(Case (e1 :: Exp p (BFin n b)) branches1)
        s2@(Case (e2 :: Exp p (BFin m b')) branches2)
    = case (eqT @(BFin n b) @(BFin m b')) of   -- check if both scrutiness have matching types
        Just Refl -> if (e1 == e2)  -- check if both scrutinees are the same
            then Case e1 (V.zipWith join branches1 branches2) -- join point-wise
            else s1 `Seq` s2        -- different scrutiness, sequence statements
        Nothing   -> s1 `Seq` s2    -- different scrut. types, sequence statements
join (s1 `Seq` s2) s3
    = (join s1 s2) `Seq` s3
join s1 s2
    = s1 `Seq` s2

joinList :: [Stmt p] -> Stmt p
joinList []       = Skip
joinList [ s ]    = s
joinList (s : ss) = join s (joinList ss)

data GenSt p = GenSt {
    fields  :: [Ex Field],
    objs    :: [Obj],
    reset   :: [Stmt p],
    seed    :: Seed
}

type Gen p = State (GenSt p)

instance Plant (GenSt p) Seed where
    plant seed = modify (\s -> s {seed = seed})

instance Plant (GenSt p) [Ex Field] where
    plant fields = modify (\s -> s {fields = fields})

instance Plant (GenSt p) [Obj] where
    plant objs = modify (\s -> s {objs = objs})

instance Plant (GenSt p) [Stmt p] where
    plant reset = modify (\s -> s {reset = reset})

instance Fresh (GenSt p) where
    getSeed = seed <$> get

-- is the given variable a state variable?
isRef :: Var a -> Gen p Bool
isRef x = do
    fields <- fields <$> get
    let isX = extract $ (== x) . coerce . fst . toTup
    return $ any isX fields

-- translate normal expressions
te :: NGExp p a -> Gen p (Exp p a)
te (NGVal _ x) = return (Val x)
te (NGVar _ x) = do
    isRefX <- isRef x
    if isRefX
        then return (Ref x)
        else return (Var x)
te (NGWhn _ e xc) = te e
te (NGAdd _ e1 e2) = Add <$> (te e1) <*> (te e2)
te (NGMul _ e1 e2) = Mul <$> (te e1) <*> (te e2)
te (NGSig _ e)     = Sig <$> (te e)
te (NGNeg _ e)     = Neg <$> (te e)
te (NGAbs _ e)     = Abs <$> (te e)
te (NGGt _ e1 e2)  = Gt <$> (te e1) <*> (te e2)

-- translates control expressions to statements
tca :: LT a => Var a -> NCA p a -> Gen p (Stmt p)
tca x (NExp e) =
    Let x <$> (te e)
tca x (NMrg _ sc branches) =
    Case (Var sc) <$> mapM (tca x) branches

getClockCA :: forall p a . CNCA p a -> Clock
getClockCA (NExp e) = getClock e
getClockCA (NMrg (_,ck) _ _) = ck

type CGen   p = Gen (p, ClockP)
type CStmt  p = Stmt (p, ClockP)
type CClass p = Class (p, ClockP)

teq :: CEQ p -> CGen p (CStmt p)
teq (LetEq x ce) = do
    ce' <- tca x ce
    return $ control (getClockCA ce) ce'
teq (FbyEq (_,ck) x v e) = do
    e' <- te e
    consTo fields (Ex $ Field (x,v))
    consTo reset  (x `Ass` (Val v))
    return $ control ck (x `Ass` e')
teq (AppEq x node args) = do
    args' <- mapM (exMapM te) args
    obj <- flip Obj node <$> freshName "obj_"
    consTo objs obj
    consTo reset (CallReset obj)
    -- This way of getting the clock `ck` is clearly a hack!
    -- It will fail if the list of args is empty
    -- To avoid this we need the equation to have been annotated
    let ck = head (map (extract getClock) args)
    return $ control ck (CallStep x obj args')

teqlist :: [CEQ p] -> CGen p [CStmt p]
teqlist eqs = foldrM go [] eqs
    where go eq accStmt = flip (:) accStmt <$> teq eq

tpN :: CEQNode p -> Seed -> (CClass p,Seed)
tpN (EQNode name args eqs res) sd = (clas, (seed resSt))
    where
        -- build translation computation
        transM = (,) <$> teqlist eqs <*> te res
        -- execute translation
        ((stmts,res'),resSt) = runState transM (GenSt [] [] [] sd)
        -- build step method
        step = Step args res' stmts
        -- build class
        clas = Class name
                    (fields resSt) (objs resSt)
                    (reset resSt) step

translateNode = tpN

localVars :: [Stmt p] -> [Ex Var]
localVars = reverse . S.toList . foldr collect S.empty
    where
    collect (Let x _)        acc = Ex x `S.insert` acc
    collect (CallStep x _ _) acc = Ex x `S.insert` acc
    collect (Seq s1 s2)      acc = collect s1 (collect s2 acc)
    collect (Case _ bs)      acc = foldr collect acc bs
    collect _                acc = acc
