{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeFamilies #-}

module Haski.Clock where

import Control.Monad.Except
import Control.Monad.RWS.Strict
import Control.Monad.State.Lazy (StateT, get, put, evalStateT)
import qualified Data.Set as S
import qualified Data.Map as Map

import Haski.Core
import Haski.Enum
import Haski.Pass
import Haski.Type
import Haski.Util
import qualified Haski.Vec as V


data Clock where
    Base    :: Clock
    On      :: (RecEnumerable n b) => Clock -> (BFin n b) -> Var (BFin n b)  -> Clock

data ClockP

type CtGExp  p = GExp (p,CkTy)
type CtGDef  p = GDef (p,CkTy)
type CtGNode p = GNode (p,CkTy)

type CGExp  p = GExp (p,ClockP)
type CGDef  p = GDef (p,ClockP)
type CGNode p = GNode (p,ClockP)

type instance ArgVal ClockP = Clock
type instance ArgVar ClockP = Clock
type instance ArgFby ClockP = Clock
type instance ArgWhn ClockP = Clock
type instance ArgMrg ClockP = Clock
type instance ArgAdd ClockP = Clock
type instance ArgMul ClockP = Clock
type instance ArgAbs ClockP = Clock
type instance ArgSig ClockP = Clock
type instance ArgNeg ClockP = Clock
type instance ArgGt  ClockP = Clock

type instance ArgGtPoly ClockP   = Clock
type instance ArgNot ClockP      = Clock
type instance ArgIfte ClockP     = Clock
type instance ArgCaseOf ClockP   = Clock
type instance ArgSym ClockP      = Clock
type instance ArgFieldExp ClockP = Clock

pattern CVal :: () => (LT a)
    => Clock -> a -> GExp ClockP a
pattern CVal c x = GVal c x

-- Clocks as types
data CkTy where
    BaseTy :: CkTy
    OnTy   :: (RecEnumerable n b) => CkTy -> BFin n b -> Var (BFin n b)  -> CkTy
    TyVar  :: Name -> CkTy

-- Clock substitution
type CkSubst = Map.Map Name CkTy
type CkEnv = CkSubst

emptySubst :: CkSubst
emptySubst = Map.empty

-------------
-- CLOCK PASS
-------------

-- run the constraint solver to produce a substitution
runSolver :: [Constraint] -> CkSubst
runSolver cs = case res of
    Left err ->
        error $ "Clock error: " ++ show err
    Right subst ->
        subst
    where
        res = runExcept $ evalStateT solve (emptySubst,cs)

-- run clock inference to generate unification constraints
runInf :: CkEnv -> InferState -> Infer a -> (a,[Constraint])
runInf env st m = case res of
    Left err ->
        error $ "Clock error: " ++ show err
    Right (ds,cs) ->
        (ds,cs)
    where
        res = runExcept (evalRWST m env st)

groundExp :: CtGExp p a -> CGExp p a
groundExp = mapSndAnn specialize
    where
    specialize :: CkTy -> Clock
    specialize BaseTy = Base
    specialize (OnTy ck c x) = On (specialize ck) c x
    specialize (TyVar _) = Base

genEnv :: Seed -> GNode p -> (CkEnv,Seed)
genEnv s (GNode name _ body _) =
    foldr go (Map.empty, s) defNames

    where
    go :: Name -> (CkEnv,Seed) -> (CkEnv,Seed)
    go name (env',s') =
        (Map.insert name (TyVar (letters !! s')) env', s'+1)

    -- names of variables defined by equations
    defNames :: [Name]
    defNames = map (getName . defines) body

    defines :: GDef p -> Ex Var
    defines (Let x _)   = Ex x
    defines (App x _ _) = Ex x

clockNode :: GNode p -> CGNode p
clockNode node = mapNode groundExp node'
    where
    -- generate initial env.
    (env,seed) = genEnv 0 node
    -- run inference and annotate node with clock
    (annNode,cs) = runInf env (InferState seed) (inferClockNode node)
    -- solve resulting constraints
    ultSubst = runSolver cs
    -- apply the solution of solving back to annotated node
    node' = apply ultSubst annNode

------------------------
-- CLOCK TYPE INFERENCE
------------------------

-- unification constraint
type Constraint = (CkTy, CkTy)

type Infer a = (RWST
                  CkEnv              -- Typing environment
                  [Constraint]       -- Generated constraints
                  InferState         -- Inference state
                  (Except TypeError) -- Type errors
                  a)                 -- Result

data InferState = InferState { count :: Int }

data TypeError = UnboundVariable String
    | UnificationMismatch CkTy CkTy
    | InfiniteType Name CkTy
    deriving Show

-- | Unify two clock types
unify :: CkTy -> CkTy -> Infer ()
unify t1 t2 = tell [(t1, t2)]

inferClockNode :: GNode p -> Infer (CtGNode p)
inferClockNode (GNode name args defs res) = do
    let argNames = map (extract getName) args
        argEnv   = zip argNames (repeat BaseTy)
    inEnv argEnv $ do
        defs' <- mapM inferClockDef defs
        res' <- inferClock res
        return (GNode name args defs' res')

inferClockDef :: GDef p -> Infer (CtGDef p)
inferClockDef (Let x e) = do
    a <- lookupEnv x
    e' <- checkClock e a
    return (Let x e')
inferClockDef (App x node args) = do
    a <- lookupEnv x
    args' <- mapM (exMapM (flip checkClock a)) args
    return (App x node args')

inferClock :: GExp p a -> Infer (CtGExp p a)
inferClock (GVal ann x) = do
    a <- freshTyVar
    return (GVal (ann,a) x)
inferClock (GVar ann x) = do
    a <- lookupEnv x
    return (GVar (ann,a) x)
inferClock (GFby ann x e) = do
    a <- freshTyVar
    e' <- checkClock e a
    return (GFby (ann,a) x e')
inferClock (GWhn ann e (x,c)) = do
    a <- lookupEnv x
    e' <- checkClock e a
    return $ GWhn (ann,OnTy a c x) e' (x,c)
inferClock (GMrg ann (x :: Var (BFin n b)) m) = do
    a <- lookupEnv x
    -- enumerate all possible values
    let cs = enumerate @n @(BFin n b)
    -- ensure that the expressions of the match
    -- are on mutually exclusive clocks
    m' <- V.zipWithM
        (\c -> flip checkClock (OnTy a c x))
        cs m
    return (GMrg (ann,a) x m')
inferClock (GAdd ann e1 e2) = do
    a <- freshTyVar
    e1' <- checkClock e1 a
    e2' <- checkClock e2 a
    return (GAdd (ann,a) e1' e2')
inferClock (GMul ann e1 e2) = do
    a <- freshTyVar
    e1' <- checkClock e1 a
    e2' <- checkClock e2 a
    return (GMul (ann,a) e1' e2')
inferClock (GAbs ann e) = do
    e' <- inferClock e
    return (GAbs (ann, getCkTy e') e')
inferClock (GSig ann e) = do
    e' <- inferClock e
    return (GSig (ann,getCkTy e') e')
inferClock (GNeg ann e) = do
    e' <- inferClock e
    return (GNeg (ann,getCkTy e') e')
inferClock (GGt ann e1 e2) = do
    a <- freshTyVar
    e1' <- checkClock e1 a
    e2' <- checkClock e2 a
    return (GGt (ann,a) e1' e2')

inferClock (GGtPoly ann e1 e2) = do
    a <- freshTyVar
    e1' <- checkClock e1 a
    e2' <- checkClock e2 a
    return (GGtPoly (ann,a) e1' e2')
inferClock (GNot ann e) = do
    a <- freshTyVar
    e' <- checkClock e a
    return (GNot (ann,a) e')
inferClock (GIfte ann b e1 e2) = do
    a <- freshTyVar
    b' <- checkClock b a
    e1' <- checkClock e1 a
    e2' <- checkClock e2 a
    return (GIfte (ann,a) b' e1' e2')
inferClock (GSym ann sid) = (\ a -> GSym (ann, a) sid) <$> freshTyVar
inferClock (GFieldExp ann tag e) = do
    a <- freshTyVar
    e' <- checkClock e a
    return $ GFieldExp (ann, a) tag e'
-- NOTE: The clocks inference for CaseOf and related expressions is not based on
-- some theory or reasoning. Rather, it's implemented entirely with a "see if it
-- seems to work"-approach.
inferClock (GCaseOf ann scrut branches) = do
    -- The approach taken here is that we use the same clock type for both the
    -- scrutinee and all branches. This seems most likely to be sensible.
    ckTy <- freshTyVar
    scrut' <- inferClockScrut ckTy scrut
    branches' <- mapM (inferClockBranch ckTy) branches
    return (GCaseOf (ann, ckTy) scrut' branches')
  where
    inferClockScrut :: CkTy -> Scrut p e -> Infer (Scrut (p, CkTy) e)
    inferClockScrut ckty (Scrut scrutE sid) = do
        scrutE' <- checkClock scrutE ckty
        pure $ Scrut scrutE' sid

    inferClockBranch :: CkTy -> Branch p b -> Infer (Branch (p, CkTy) b)
    inferClockBranch ckty (Branch predE bodyE) = do
        predE' <- checkClock predE ckty
        bodyE' <- checkClock bodyE ckty
        pure $ Branch predE' bodyE'

-- Check that an expression has a given clock
checkClock :: GExp p a -> CkTy -> Infer (CtGExp p a)
checkClock e a = do
    e' <- inferClock e
    unify a (getCkTy e')
    return e'

-- lookup the clock type of a variable
lookupEnv :: Var a -> Infer CkTy
lookupEnv x = do
    env <- ask
    case Map.lookup (getName x) env of
        Nothing -> throwError $ UnboundVariable (getName x)
        Just ty  -> return ty

letters :: [String]
letters = [1..] >>= flip replicateM ['a'..'z']

-- generate a fresh type-variable name
freshTyVar :: Infer CkTy
freshTyVar = do
  s <- get
  put s{count = count s + 1}
  return $ TyVar (letters !! count s)

--------------------
-- CONSTRAINT SOLVER
--------------------

type Unifier = (CkSubst, [Constraint])

type Solve a = StateT Unifier (Except TypeError) a

-- | solve constraints
solve :: Solve CkSubst
solve = do
  (su, cs) <- get
  case cs of
    [] -> return su
    ((a, b): cs') -> do
        su'  <- unifies a b
        put (su' `compose` su, map (apply su') cs')
        solve

-- | unifies two types and generates a substitution
unifies :: CkTy -> CkTy -> Solve CkSubst
unifies BaseTy BaseTy = return emptySubst
unifies (OnTy a c x) (OnTy b c' y) = do
    sub <- unifies a b
    if enumVal c == enumVal c'
        && getName x == getName y
    then return sub
    else throwError $ UnificationMismatch (OnTy a c x) (OnTy b c' y)
unifies (TyVar x) a = x `bind` a
unifies a (TyVar x) = x `bind` a
unifies a b = throwError $ UnificationMismatch a b

-- | generates a substitution by binding a
-- | a given variable name to a given type
bind :: Name -> CkTy -> Solve CkSubst
bind x a
    | TyVar x == a = return emptySubst
    | occurs x a   = throwError $ InfiniteType x a
    | otherwise    = return $ Map.singleton x a

-- | performs occurs check
occurs :: Name -> CkTy -> Bool
occurs x a = x `S.member` (fv a)

-- | compose two substitutions
compose :: CkSubst -> CkSubst -> CkSubst
s1 `compose` s2 = Map.map (apply s1) s2 `Map.union` s1

-----------------
-- BOOTSTRAPPING
-----------------


-- | Extend type environment in Infer
inEnv :: [(Name, CkTy)] -> Infer a -> Infer a
inEnv ntys m = do
  let scope env = env `Map.union` (Map.fromList ntys)
  local scope m

---------------
-- BOILERPLATE
---------------

-- | free variables in a type
fv :: CkTy -> S.Set Name
fv = go S.empty
    where
    go s BaseTy = s
    go s (OnTy a c x) = go s a
    go s (TyVar x) = x `S.insert` s

class Substitutable a where
    apply :: CkSubst -> a -> a

instance Substitutable (CtGDef p) where
    apply s (Let x e) =
        Let x (apply s e)
    apply s (App x name args) =
        App x name (map (exMap (apply s)) args)

instance Substitutable (CtGNode p) where
    apply s (GNode name args body res) =
        GNode name args (map (apply s) body) (apply s res)

instance Substitutable CkTy where
    apply s BaseTy = BaseTy
    apply s (OnTy a x c) = OnTy (apply s a) x c
    apply s a@(TyVar x) = Map.findWithDefault a x s

instance Substitutable Constraint where
    apply s (a , b) = (apply s a, apply s b)

instance Substitutable (CtGExp p a) where
    apply s e = mapSndAnn (apply s) e

-- | Get the (top-level) clock of an expression
getCkTy :: GExp (p,CkTy) a -> CkTy
getCkTy = getAnn . snd . unpack

type instance ArgVal CkTy = CkTy
type instance ArgVar CkTy = CkTy
type instance ArgFby CkTy = CkTy
type instance ArgWhn CkTy = CkTy
type instance ArgMrg CkTy = CkTy
type instance ArgAdd CkTy = CkTy
type instance ArgMul CkTy = CkTy
type instance ArgAbs CkTy = CkTy
type instance ArgSig CkTy = CkTy
type instance ArgNeg CkTy = CkTy
type instance ArgGt  CkTy = CkTy

type instance ArgGtPoly CkTy   = CkTy
type instance ArgNot CkTy      = CkTy
type instance ArgIfte CkTy     = CkTy
type instance ArgCaseOf CkTy   = CkTy
type instance ArgSym CkTy      = CkTy
type instance ArgFieldExp CkTy = CkTy

instance Eq CkTy where
    BaseTy == BaseTy
        = True
    OnTy a c x == OnTy b c' y
        = enumVal c == enumVal c'
            && getName x == getName y
            && a == b
    TyVar x == TyVar y
        = x == y
    _  == _
        = False

instance Show CkTy where
    show BaseTy        = "Base"
    show (OnTy cl c v) = "On" ++ " " ++ show cl
        ++ " " ++ show c ++ " {" ++ (getName v) ++ "}"
    show (TyVar x)     = "(Var" ++ " " ++ x ++ ")"
