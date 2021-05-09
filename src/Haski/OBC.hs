-- TODO: Clean up stuff from the CaseOf addition (imports etc.)

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TupleSections #-}

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

import Data.Bifunctor (second)
import Data.Coerce (coerce)
import Data.Foldable (foldrM, fold)
import Data.Maybe (isJust)
import Data.Proxy (Proxy(..))
import Data.Typeable (Typeable, eqT)
import qualified Data.Map.Strict as M
import qualified Data.Set as S

import Control.Monad.Reader hiding (join)
import Control.Monad.State.Lazy (State, StateT, get, runState, execState, modify, modify')

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

-- | Function definition for handling the logic of a pattern match.
data CaseDef p = forall retTy . (LT retTy) => CaseDef
    (Proxy retTy)  -- ^ Return type
    [HVar]        -- ^ Function params
    [Stmt p]       -- ^ Function body

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

    If     :: Exp p Bool -> [Stmt p] -> Stmt p
    Return :: Exp p a -> Stmt p

data Exp p a where
    -- "simple" variable
    Var :: Var a -> Exp p a
    -- reference variable (`Ref x` represents "store(x)")
    Ref :: Var a -> Exp p a
    Val :: LT a => a -> Exp p a
    Add :: Exp p a -> Exp p a -> Exp p a
    Mul :: Exp p a -> Exp p a -> Exp p a
    Sig :: Exp p a -> Exp p a
    Neg :: Exp p a -> Exp p a
    Abs :: Exp p a -> Exp p a
    Gt  :: Exp p Int -> Exp p Int -> Exp p Bool

    -- Function call to pattern matching function (argument and function name).
    CaseOfCall :: (LT a, LT b)
        => Exp p a  -- ^ Scrutinee expression
        -> String   -- ^ Function name
        -> [HVar]  -- ^ Other function arguments. These are variables which
                    --   are expected to be in scope at the call site.
        -> Exp p b
    Sym :: ScrutId -> Exp p a

deriving instance Eq (Var a)
deriving instance Ord (Var a)

-- deriving instance Eq (Exp p a)

-- Most cases are trivial, but the CaseOf constructor needs to check if types
-- of its arguments (that are not the 'b' in return 'Exp p b') are equal too.
instance Eq a => Eq (Exp p a) where
    Var v     == Var w       = v == w
    Ref v     == Ref w       = v == w
    Val x     == Val w       = x == w
    Add e1 e2 == Add e1' e2' = e1 == e1' && e2 == e2'
    Mul e1 e2 == Mul e1' e2' = e1 == e1' && e2 == e2'
    Sig e     == Sig e'      = e == e'
    Neg e     == Neg e'      = e == e'
    Abs e     == Abs e'      = e == e'
    Gt n1 n2  == Gt m1 m2    = n1 == m1 && n2 == m2
    -- Function calls to pattern matching functions are never equal for now
    CaseOfCall{} == CaseOfCall{} = False
    Sym s     == Sym s'      = s == s'

    _ == _ = False

-- These are basically copies of types from "Haski.Core", but contains 'Exp'
-- instead of 'Haski.Core.GExp'.
data Scrut p a = LT a => Scrut (Exp p a) ScrutId
type ScrutId = String
deriving instance Eq a => Eq (Scrut p a)

data Branch p t b = LT b => Branch (Exp p Bool) (Exp p b)
deriving instance Eq b => Eq (Branch p t b)

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

type CaseOfDefs p = M.Map String (CaseDef p)

data GenSt p = GenSt
    { fields  :: [Ex Field]
    , objs    :: [Obj]
    , reset   :: [Stmt p]
    , seed    :: Seed

    , funDefs :: CaseOfDefs p
    -- ^ Function definitions used to handle pattern matching logic. These are
    -- generated during translation of expressions. The mapping is from the
    -- name of the function to its definition
    }

type Gen p = State (GenSt p)

instance Plant (GenSt p) Seed where
    plant seed = modify (\s -> s {seed = seed})
    -- 'plant seed', lol

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
te (NGSym _ sid) = pure $ Sym sid
te (NGCaseOf
    _
    (scrut    :: Core.Scrut (p, NormP) scrutTy)
    (branches :: [Core.Branch (p, NormP) a]))
    = do
        -- Generate the definition of the pattern matching function and add
        -- it to the compilation state.
        (funName, def, inScopeVars) <- newCaseDef branches
        modify $ \ st -> st { funDefs = M.insert funName def (funDefs st) }

        -- Translate the scrutinee expression, it will be the argument to the
        -- call to the pattern matching function.
        let Core.Scrut e sid = scrut
        e' <- te e
        let funCall = CaseOfCall e' funName inScopeVars

        pure funCall
  where
    newCaseDef :: [Core.Branch (p, NormP) b] -> Gen p (String, CaseDef p, [HVar])
    newCaseDef bs = do
        funName <- freshName "fun"
        let scrutParam = HVar $ Core.MkVar @scrutTy ("__ARGUMENT", Nothing)

        retVar <- Core.MkVar . (, Nothing) <$> freshName "retVar"
        (ifs, vars) <- unzip <$> mapM (mkIf retVar) bs
        let inScopeVars = S.elems (S.unions vars)
        let funBody = ifs
        pure ( funName
             , CaseDef (Proxy @a) (scrutParam : inScopeVars) funBody
             , inScopeVars
             )

    mkIf :: Var a -> Core.Branch (p, NormP) b -> Gen p (Stmt p, S.Set HVar)
    mkIf retVar (Core.Branch cond body) = do
        cond' <- te cond
        body' <- te body

        -- Find all variables used inside the function body so we can provide
        -- the caller with the correct arguments.
        let vars = collectVars body'

        pure (If cond' [Return body'], vars)

    collectVars :: forall p b . LT b => Exp p b -> S.Set HVar
    collectVars = go S.empty
      where
        go :: LT c => S.Set HVar -> Exp p c -> S.Set HVar
        go vars = \case
            Var v   -> HVar v `S.insert` vars
            -- Ref v might be questionable
            Ref v   -> HVar v `S.insert` vars
            Add x y -> go (go vars x) y
            Mul x y -> go (go vars x) y
            Sig e   -> go vars e
            Neg e   -> go vars e
            Abs e   -> go vars e
            Gt  x y -> go (go vars x) y
            CaseOfCall e _ _ -> go vars e
            Val{}   -> vars
            Sym{}   -> vars

-- Used for heterogeneous structures of typed variables.
data HVar = forall a . LT a => HVar (Var a)

instance Eq HVar where
    HVar (Core.MkVar x) == HVar (Core.MkVar y) = x == y

instance Ord HVar where
    HVar (Core.MkVar x) <= HVar (Core.MkVar y) = x <= y

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

tpN :: CEQNode p -> Seed -> ((CClass p, CaseOfDefs (p, ClockP)), Seed)
tpN (EQNode name args eqs res) sd = ((clas, caseOfDefs), seed resSt)
    where
        -- build translation computation
        transM = (,) <$> teqlist eqs <*> te res
        -- execute translation
        ((stmts,res'),resSt) = runState transM (GenSt [] [] [] sd M.empty)
        -- build step method
        step = Step args res' stmts
        -- build class
        clas = Class name
                    (fields resSt) (objs resSt)
                    (reset resSt) step

        -- Stuff needed to generate code for pattern matching functions.
        caseOfDefs = funDefs resSt

translateNode = tpN

localVars :: [Stmt p] -> [Ex Var]
localVars = reverse . S.toList . foldr collect S.empty
    where
    collect (Let x _)        acc = Ex x `S.insert` acc
    collect (CallStep x _ _) acc = Ex x `S.insert` acc
    collect (Seq s1 s2)      acc = collect s1 (collect s2 acc)
    collect (Case _ bs)      acc = foldr collect acc bs
    collect _                acc = acc
