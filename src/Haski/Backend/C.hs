-- TODO: Need a primer on how the code is generated :D
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

{- | C-backend code generation.

Note that the CaseOf-style pattern matching implementation (not the one using
Merge) is hacky as all hell, and its generated function calls make some bold
assumptions about variables being in scope at the call site.
-}

module Haski.Backend.C where

import Data.Foldable (Foldable(fold))
import Data.Functor ((<&>))
import Data.Proxy (Proxy(..))
import Text.PrettyPrint.HughesPJClass (Pretty(..))

import qualified Control.Monad.State.Strict as St
import qualified Data.Map.Strict as M

import Haski.OBC (Class(..), Field(..), Obj(..), Step(..) )
import qualified Haski.OBC as OBC
import Haski.Type
import Haski.Util
import Haski.Core (Var, RecEnumerable)
import Haski.Backend
import Haski.Enum
import qualified Haski.Vec as V

import Language.C99.Simple.AST
import qualified Language.C99.Simple.AST as C
import Language.C99.Simple.Translate
import Language.C99.Simple.Expr

import qualified Language.C99.AST as C99.AST (TransUnit)
import qualified Language.C99.Pretty as C99.Pretty (pretty)


cType :: forall a . LT a => C.Type
cType = TypeSpec $ case (typeRepLT @a) of
    TUnit -> Char
    TBool -> Int
    TInt8 -> Int
    TInt  -> Int
    TBFin -> Unsigned_Short
    TUDef -> Unsigned_Short

instance Pretty C99.AST.TransUnit where
    pPrint = C99.Pretty.pretty

instance Semigroup TransUnit where
    TransUnit d1 f1 <> TransUnit d2 f2 = TransUnit (d1 ++ d2) (f1 ++ f2)

instance Monoid TransUnit where
    mempty = TransUnit [] []

-- Ignoring the use of the Backend interface here, since it doesn't quite
-- do what we want.
compilePlusCaseOfDefs :: ([Class p], [OBC.CaseOfDefs p1]) -> C99.AST.TransUnit
compilePlusCaseOfDefs (cs, defs) = flip St.evalState initState $ do
    TransUnit ds fs <- fold <$> mapM cTransUnitFromClass cs
    caseOfDefs <- concat <$> mapM cCaseOfDefs defs

    let cUnit = TransUnit ds (fs ++ caseOfDefs)
    pure $ translate cUnit
  where
    initState :: Cst
    initState = Cst
        { cstGlobals = M.empty
        }

    mkVarDecln :: (C.Ident, C.Type) -> Decln
    mkVarDecln (i, t) = C.VarDecln Nothing t i Nothing

cTransUnitFromClass :: Class p -> Compile TransUnit
cTransUnitFromClass (Class name fields instances reset step) = do
    stepFunDef <- genStepFun name step
    resetFunDef <- genResetFun name reset
    pure $ TransUnit [TypeDecln memStruct] [resetFunDef, stepFunDef]
  where
    memStruct = genMemStruct name fields instances

-- | Compile an OBC representation of a pattern matching function into the
-- C99.Simple AST representation.
cCaseOfDefs :: OBC.CaseOfDefs p -> Compile [C.FunDef]
cCaseOfDefs = mapM (uncurry cCaseOfDef) . M.assocs

cCaseOfDef :: String -> OBC.CaseDef p -> Compile C.FunDef
cCaseOfDef
    funName
    (OBC.CaseDef (Proxy :: Proxy retTy) obcParams fieldExps stmts)
  = do
    declns <- mapM (uncurry mkDecln) $ M.assocs fieldExps
    stmts' <- mapM genCStmt stmts
    pure $ FunDef (cType @retTy) funName (map tlHVar obcParams) declns stmts'
  where
    tlHVar :: OBC.HVar -> Param
    tlHVar (OBC.HVar (var :: Var a)) = Param (cType @a) (getName var)

    -- Create a declaration for a named expression.
    mkDecln :: Name -> Ex (OBC.Exp p) -> Compile Decln
    mkDecln name (Ex (e :: OBC.Exp p a)) = do
        ce <- genCExpr e
        pure $ VarDecln Nothing (cType @a) name (Just (InitExpr ce))

-- for debugging only
instance Show (OBC.CaseDef p) where
    show (OBC.CaseDef (Proxy :: Proxy retTy) obcParams fieldExps stmts) =
        undefined
        -- "argTy: " ++ show (cType @argTy)

-- for debugging only
deriving instance Show C.Type
deriving instance Show C.Expr
deriving instance Show C.AssignOp
deriving instance Show C.Init
deriving instance Show C.UnaryOp
deriving instance Show C.BinaryOp
deriving instance Show C.TypeName
deriving instance Show C.TypeSpec
deriving instance Show C.FieldDecln

voidC = Type (TypeSpec Void)

genResetFun :: Name -> [OBC.Stmt p] -> Compile FunDef
genResetFun name body = do
    -- components of the function
    let funName     = name ++ "_reset"
    let selfParam   = Param (Type selfType) "self"
    funBody <- mapM genCStmt body
    -- HACK: because the C library doesn't allow empty function body
    let funBodyHack = if null funBody then [skipC] else funBody

    pure $ FunDef voidC funName [selfParam] [] funBodyHack
  where
    -- Types
    selfType :: Type
    selfType = Ptr (TypeSpec $ Struct (name ++ "_mem"))

genStepFun :: Name -> Step p -> Compile FunDef
genStepFun name (Step params (res :: OBC.Exp p a) body) = do
    -- components of the function
    let funName     = name ++ "_step"
    let selfParam   = Param (Type selfType) "self"
    let stepParams  = map (extract $ fromVar @Param) params
    returnExpr <- Return . Just <$> genCExpr res
    funBody <- mapM genCStmt body <&> (++ [returnExpr])
    let localDeclns = map (extract $ fromVar @Decln) (OBC.localVars body)

    pure $ FunDef resType funName (selfParam : stepParams) localDeclns funBody
  where
    -- Types
    resType, selfType :: Type
    resType  = Type (cType @a)
    selfType = Ptr (TypeSpec $ Struct (name ++ "_mem"))

-- converts a list of fields to a struct definition
genMemStruct :: Name -> [Ex Field] -> [Obj] -> Type
genMemStruct className fields insts =
    TypeSpec $ StructDecln
        (Just structName)
        (fieldDeclnsHack ++ instDeclns)
    where
    structName       = className ++ "_mem"
    fieldDeclns      = map mkFieldDecln fields
    instDeclns       = map mkInstDecln insts
    -- HACK: because the C library doesn't allow empty structs
    fieldDeclnsHack  = if (null fieldDeclns)
        then [ FieldDecln (Ptr voidC) "dead" ]
        else fieldDeclns

    mkFieldDecln f = extract (fromVar @FieldDecln . fst . toTup) f
    mkInstDecln  o = FieldDecln (getFieldType o) (getName o)
    getFieldType o = Ptr . TypeSpec . Struct $ (objType o) ++ "_mem"

valRepC :: forall n b . (BFin n b) -> C.Expr
valRepC = LitInt . toInteger . enumVal

genCVal :: forall a . LT a => a -> C.Expr
genCVal x = case typeRepLT @a of
    TUnit   -> LitInt 1
    TBool   -> LitInt (if x then 1 else 0)
    TInt8   -> LitInt $ toInteger x
    TInt    -> LitInt $ toInteger x
    TBFin   -> valRepC x
    TUDef   -> valRepC (toBFin x)

signumC :: C.Expr -> C.Expr
signumC x = (x .> (LitInt 0)) .- (x .> (LitInt 0))

absC :: C.Expr -> C.Expr
absC x = Funcall (Ident "abs") [x]

selfC :: C.Expr
selfC = Ident "self"

-- x -> f
(.->) :: C.Expr -> Ident -> C.Expr
(.->) x f = Dot (deref x) f

genCExpr :: OBC.Exp p a -> Compile C.Expr
genCExpr (OBC.Var x)     = pure $ Ident $ getName x
genCExpr (OBC.Ref x)     = pure $ selfC .-> getName x
genCExpr (OBC.Val x)     = pure $ genCVal x
genCExpr (OBC.Add e1 e2) = (.+) <$> genCExpr e1 <*> genCExpr e2
genCExpr (OBC.Mul e1 e2) = (.*) <$> genCExpr e1 <*> genCExpr e2
genCExpr (OBC.Neg e)     = neg <$> genCExpr e
genCExpr (OBC.Sig e)     = signumC <$> genCExpr e
genCExpr (OBC.Abs e)     = absC <$> genCExpr e
genCExpr (OBC.Gt e1 e2)  = (.>) <$> genCExpr e1 <*> genCExpr e2
genCExpr (OBC.Sym sid)   = pure $ Ident sid
genCExpr (OBC.CaseOfCall e f inScopeVars) = do
    e' <- genCExpr e
    let args = e' : map (\ (OBC.HVar var) -> Ident $ getName var) inScopeVars
    pure $ Funcall (Ident f) args

caseC :: forall n b . RecEnumerable n b => C.Expr -> V.Vec n C.Stmt -> C.Stmt
caseC scrut = Switch scrut . V.toList . V.zipWith mkCase (enumerate @n @(BFin n b))
    where
    mkCase x branch = C.Case (valRepC x) (seqStmtC [branch,Break])

-- HACK: because there's no way to make stmt. blocks in the C lib.
seqStmtC :: [C.Stmt] -> C.Stmt
seqStmtC stms = If (LitBool True) stms

skipC :: C.Stmt
skipC = Expr $ Cast (TypeName (TypeSpec Void)) (LitInt 0)

genCStmt :: OBC.Stmt p -> Compile C.Stmt
genCStmt (OBC.Let x e) = do
    e' <- genCExpr e
    pure $ Expr $ Ident (getName x) .= e'
genCStmt (OBC.Ass x e) = do
    e' <- genCExpr e
    pure $ Expr $ (selfC .-> getName x) .= e'
genCStmt OBC.Skip = pure skipC
genCStmt (OBC.Seq s1 s2) = seqStmtC <$> mapM genCStmt [s1, s2]
genCStmt (OBC.Case (scrut :: OBC.Exp p (BFin n b)) branches) = do
    scrut' <- genCExpr scrut
    branches' <- mapM genCStmt branches
    pure $ caseC @n @b scrut' branches'
-- classname_reset(self->objname)
genCStmt (OBC.CallReset obj) = pure $ Expr
    $ Funcall (Ident (objType obj ++ "_reset")) [Ident "self" .-> getName obj]
genCStmt (OBC.CallStep x obj args) = do
    args' <- mapM (extract genCExpr) args
    let selfDeref = Ident "self" .-> getName obj : args'
    let funCall = Funcall (Ident (objType obj ++ "_step")) selfDeref
    pure $ Expr $ Ident (getName x) .= funCall
genCStmt (OBC.If cond stmts) = If <$> genCExpr cond <*> mapM genCStmt stmts
genCStmt (OBC.Return retExp) = Return . Just <$> genCExpr retExp

class FromVar b where
    fromVar :: LT a => Var a -> b

instance FromVar FieldDecln where
    fromVar (x :: Var a) = FieldDecln (cType @a) (getName x)

instance FromVar Param where
    fromVar (x :: Var a) = Param (cType @a) (getName x)

instance FromVar Decln where
    fromVar (x :: Var a) = VarDecln Nothing (cType @a) (getName x) Nothing

--
-- Functions related to the compilation state
--

-- | Compilation state.
newtype Cst = Cst
    { cstGlobals :: M.Map C.Ident C.Type
    -- ^ Global variables and their types, accumulated during code generation.
    }
type Compile = St.State Cst
