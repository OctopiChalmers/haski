-- TODO: Need a primer on how the code is generated :D
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE StandaloneDeriving #-}

module Haski.Backend.C where

import Data.Proxy (Proxy(..))
import Text.PrettyPrint.HughesPJClass (Pretty(..))

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

import Debug.Trace


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

instance Backend C99.AST.TransUnit where
    compileClasses = translate . foldr1 joinCTransUnit . map cTransUnitFromClass

-- Ignoring the use of the Backend interface here, since it doesn't quite
-- do what we want.
compilePlusCaseOfDefs (cs, defs) =
    translate $ TransUnit declns (fundefs ++ caseOfDefs)
  where
    TransUnit declns fundefs = cClasses cs

    cClasses :: [Class p] -> C.TransUnit
    cClasses = foldr1 joinCTransUnit . map cTransUnitFromClass

    caseOfDefs :: [C.FunDef]
    caseOfDefs = concatMap cCaseOfDefs defs

cTransUnitFromClass :: Class p -> C.TransUnit
cTransUnitFromClass (Class name fields instances reset step) =
    TransUnit [TypeDecln memStruct] [resetFunDef, stepFunDef]
    where
        memStruct   = genMemStruct name fields instances
        resetFunDef = genResetFun name reset
        stepFunDef  = genStepFun name step

joinCTransUnit :: TransUnit -> TransUnit -> C.TransUnit
joinCTransUnit (TransUnit decls1 defs1) (TransUnit decls2 defs2) =
    TransUnit (decls1 ++ decls2) (defs1 ++ defs2)

-- | Compile an OBC representation of a pattern matching function into the
-- C99.Simple AST representation.
cCaseOfDefs :: OBC.CaseOfDef p -> [C.FunDef]
cCaseOfDefs = map (uncurry cCaseOfDef) . M.assocs

cCaseOfDef :: String -> OBC.CaseDef p -> C.FunDef
cCaseOfDef
    funName
    (OBC.CaseDef (Proxy :: Proxy argTy) (Proxy :: Proxy retTy) stmts) =
        -- FunDef Type Ident ([Param]) ([Decln]) ([Stmt])
        FunDef (cType @retTy) funName params [] statements
  where
    params :: [Param]
    params = [Param (cType @argTy) "ARGUMENT"]

    statements :: [Stmt]
    statements = map genCStmt stmts

-- for debugging only
instance Show (OBC.CaseDef p) where
    show (OBC.CaseDef (Proxy :: Proxy argTy) (Proxy :: Proxy retTy) stmts) =
        "argTy: " ++ show (cType @argTy)

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

genResetFun :: Name -> [OBC.Stmt p] -> FunDef
genResetFun name body =
    FunDef voidC funName [selfParam] [] funBodyHack
    where
        -- components of the function
        funName     = name ++ "_reset"
        selfParam   = Param (Type selfType) "self"
        funBody     = map genCStmt body
        -- HACK: because the C library doesn't allow empty function body
        funBodyHack = if null funBody
            then [skipC]
            else funBody

        -- types
        selfType    = Ptr (TypeSpec $ Struct (name ++ "_mem"))

genStepFun :: Name -> Step p -> FunDef
genStepFun name (Step params (res :: OBC.Exp p a) body) =
    FunDef resType funName (selfParam : stepParams) localDeclns funBody
    where
        -- components of the function
        funName     = name ++ "_step"
        selfParam   = Param (Type selfType) "self"
        stepParams  = map (extract $ fromVar @Param) params
        funBody     = map genCStmt body ++ [returnExpr]
        returnExpr  = Return (Just $ genCExpr res)
        localDeclns = map (extract $ fromVar @Decln) (OBC.localVars body)

        -- types
        resType       = Type (cType @a)
        selfType    = Ptr (TypeSpec $ Struct (name ++ "_mem"))

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

genCExpr :: OBC.Exp p a -> C.Expr
genCExpr (OBC.Var x)     = Ident $ getName x
genCExpr (OBC.Ref x)     = selfC .-> (getName x)
genCExpr (OBC.Val x)     = genCVal x
genCExpr (OBC.Add e1 e2) = (genCExpr e1) .+ (genCExpr e2)
genCExpr (OBC.Mul e1 e2) = (genCExpr e1) .* (genCExpr e2)
genCExpr (OBC.Neg e)     = neg $ genCExpr e
genCExpr (OBC.Sig e)     = signumC $ genCExpr e
genCExpr (OBC.Abs e)     = absC $ genCExpr e
genCExpr (OBC.Gt e1 e2)  = (genCExpr e1) .> (genCExpr e2)
genCExpr (OBC.Sym sid)   = Ident sid
genCExpr (OBC.Call e f)  = Funcall (Ident f) [genCExpr e]

caseC :: forall n b . RecEnumerable n b => C.Expr -> V.Vec n (C.Stmt) -> C.Stmt
caseC scrut = Switch scrut . V.toList . V.zipWith mkCase (enumerate @n @(BFin n b))
    where
    mkCase x branch = C.Case (valRepC x) (seqStmtC [branch,Break])

-- HACK: because there's no way to make stmt. blocks in the C lib.
seqStmtC :: [C.Stmt] -> C.Stmt
seqStmtC stms = If (LitBool True) stms

skipC :: C.Stmt
skipC = Expr $ Cast (TypeName (TypeSpec Void)) (LitInt 0)

genCStmt :: OBC.Stmt p -> C.Stmt
genCStmt (OBC.Let x e) =
    Expr $ (Ident $ getName x) .= (genCExpr e)
genCStmt (OBC.Ass x e) =
    Expr $ (selfC .-> (getName x)) .= (genCExpr e)
genCStmt (OBC.Skip) =
    skipC
genCStmt (OBC.Seq s1 s2) =
    seqStmtC  [genCStmt s1, genCStmt s2]
genCStmt (OBC.Case (scrut :: OBC.Exp p (BFin n b)) branches) =
    caseC @n @b (genCExpr scrut) (fmap genCStmt branches)
genCStmt (OBC.CallReset obj) =
    -- classname_reset(self->objname)
    Expr $ Funcall (Ident (objType obj ++ "_reset"))
        [Ident "self" .-> (getName obj)]
genCStmt (OBC.CallStep x obj args) =
    Expr $ (Ident $ getName x) .= (Funcall (Ident (objType obj ++ "_step")) $
        (Ident "self" .-> (getName obj))
            : map (extract genCExpr) args)
genCStmt (OBC.If cond stmts) = If (genCExpr cond) (map genCStmt stmts)
genCStmt (OBC.Return retExp) = Return $ Just $ genCExpr retExp

class FromVar b where
    fromVar :: LT a => Var a -> b

instance FromVar FieldDecln where
    fromVar (x :: Var a) = FieldDecln (cType @a) (getName x)

instance FromVar Param where
    fromVar (x :: Var a) = Param (cType @a) (getName x)

instance FromVar Decln where
    fromVar (x :: Var a) = VarDecln Nothing (cType @a) (getName x) Nothing
