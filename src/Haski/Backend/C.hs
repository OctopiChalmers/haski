{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}

{- | C-backend code generation.

Note that the CaseOf-style pattern matching implementation (not the one using
Merge) is pretty hacky, and its generated function calls make some assumptions
about which variables are in scope at the call site. Currently, any Haskell
variables used inside a @caseof@ body should be in scope in the generated code,
but this may not be the case of the behavior/syntax/definition of nodes change.

For example:

> pm1 = node "pmnode" $ \ ns bs -> mdo
>     y <- alts
>     boolStream <- ns `caseof` \case
>         T1 n b -> bs  -- <- Here!

Referencing @bs@ inside the body of the @caseof@ is fine, because @bs@ will
be in scope in the surrounding generated C. Same thing with @y@. However, if
the definition of 'Haski.Lang.node' changes, and another Streams argument
is introduced which won't be in scope in the generated code, referencing it
inside the @caseof@ body will still compile, but the generated C code will not.
-}

module Haski.Backend.C where

import Data.Foldable (Foldable(fold))
import Text.PrettyPrint.HughesPJClass (Pretty(..))
import Data.Proxy (Proxy(..))
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
    TUnit   -> Char
    TBool   -> Int
    TInt8   -> Int
    TInt    -> Int
    TBFin   -> Unsigned_Short
    TUDef   -> Unsigned_Short
    TDouble -> Double  -- Idk if this is the proper representation

instance Pretty C99.AST.TransUnit where
    pPrint = C99.Pretty.pretty

instance Semigroup TransUnit where
    TransUnit d1 f1 <> TransUnit d2 f2 = TransUnit (d1 ++ d2) (f1 ++ f2)

instance Monoid TransUnit where
    mempty = TransUnit [] []

-- | Main entry point for code generation.
--
-- Ignoring the use of the Backend interface here, since its type doesn't quite
-- fit what we want; we need to send information to the code generator
-- _besides_ the OBC.Class structures.
compileFromOBC :: ([Class p], [OBC.CaseOfInfo p1]) -> C99.AST.TransUnit
compileFromOBC (oClasses, oCaseOfInfos) = translate cUnit
  where
    cUnit :: TransUnit
    cUnit = fold
        $  map cTransUnitFromClass oClasses
        <> map cTransUnitFromCaseOfInfo oCaseOfInfos

-- | Convert a mapping of OBC CaseOf function definitions into a C99.Simple
-- TransUnit that can be used to emit C.
cTransUnitFromCaseOfInfo :: OBC.CaseOfInfo p -> TransUnit
cTransUnitFromCaseOfInfo oCaseOfInfo =
    let funs    = map (uncurry cCaseOfDef) . M.assocs $ oCaseOfDefs
        declns  = map (\(FunDef t s ps _ _) -> FunDecln Nothing t s ps) funs
            <> map (extract cDeclnFromVar) exVars
        -- We need to derive the function declarations so that funcions
        -- can be called before they are defined.
    in TransUnit declns funs
  where
    (oCaseOfDefs, exVars) = (\(OBC.CaseOfInfo x ys) -> (x, ys)) oCaseOfInfo

    cDeclnFromVar :: forall a . LT a => Var a -> Decln
    cDeclnFromVar v = VarDecln Nothing (cType @a) (getName v) Nothing

    cCaseOfDefs :: OBC.CaseOfDefs p -> [C.FunDef]
    cCaseOfDefs = map (uncurry cCaseOfDef) . M.assocs

-- | Convert an OBC Class into a C99.Simple TransUnit that can be used to
-- emit C.
cTransUnitFromClass :: Class p -> TransUnit
cTransUnitFromClass (Class name fields instances reset step) =
    let stepFunDef  = genStepFun name step
        resetFunDef = genResetFun name reset
    in TransUnit [TypeDecln memStruct] [resetFunDef, stepFunDef]
  where
    memStruct = genMemStruct name fields instances

-- | Compile an OBC representation of a pattern matching function into the
-- C99.Simple AST representation.
cCaseOfDef :: Name -> OBC.CaseDef p -> C.FunDef
cCaseOfDef
    funName
    (OBC.CaseDef (Proxy :: Proxy retTy) obcParams globalScrutName fieldExps stmts)
  = let scrutAss = mkScrutAss globalScrutName (head obcParams)  -- yikes
        fieldAssignments = map (uncurry mkFieldAss) $ M.assocs fieldExps
        stmts' = scrutAss : fieldAssignments <> map genCStmt stmts
    in FunDef (cType @retTy) funName (map mkParam obcParams) [] stmts'
  where
    mkScrutAss :: Name -> Ex Var -> Stmt
    mkScrutAss s ex = Expr $
        AssignOp Assign (Ident s) (extract (Ident . getName) ex)

    mkParam :: Ex Var -> Param
    mkParam (Ex (var :: Var a)) = Param (cType @a) (getName var)

    mkFieldAss :: Name -> Ex (OBC.Exp p) -> Stmt
    mkFieldAss name (Ex (e :: OBC.Exp p a)) =
        let ce = genCExpr e
        in Expr $ AssignOp Assign (Ident name) ce

voidC :: Type
voidC = Type (TypeSpec Void)

genResetFun :: Name -> [OBC.Stmt p] -> FunDef
genResetFun name body =
    let
        -- components of the function
        funName   = name ++ "_reset"
        selfParam = Param (Type selfType) "self"
        funBody   = map genCStmt body
        -- HACK: because the C library doesn't allow empty function body
        funBodyHack = if null funBody then [skipC] else funBody
    in FunDef voidC funName [selfParam] [] funBodyHack
  where
    -- Types
    selfType :: Type
    selfType = Ptr (TypeSpec $ Struct (name ++ "_mem"))

genStepFun :: Name -> Step p -> FunDef
genStepFun name (Step params (res :: OBC.Exp p a) body) =
    -- components of the function
    let funName     = name ++ "_step"
        selfParam   = Param (Type selfType) "self"
        stepParams  = map (extract $ fromVar @Param) params
        returnExpr  = Return . Just $ genCExpr res
        funBody     = map genCStmt body ++ [returnExpr]
        localDeclns = map (extract $ fromVar @Decln) (OBC.localVars body)
    in FunDef resType funName (selfParam : stepParams) localDeclns funBody
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
    TDouble -> LitDouble x

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
genCExpr (OBC.Ref x)     = selfC .-> getName x
genCExpr (OBC.Val x)     = genCVal x
genCExpr (OBC.Add e1 e2) = genCExpr e1 .+ genCExpr e2
genCExpr (OBC.Mul e1 e2) = genCExpr e1 .* genCExpr e2
genCExpr (OBC.Neg e)     = neg $ genCExpr e
genCExpr (OBC.Sig e)     = signumC $ genCExpr e
genCExpr (OBC.Abs e)     = absC $ genCExpr e
genCExpr (OBC.Gt e1 e2)  = genCExpr e1 .> genCExpr e2

genCExpr (OBC.GtPoly e1 e2) = genCExpr e1 .> genCExpr e2
genCExpr (OBC.Eq e1 e2)     = genCExpr e1 .== genCExpr e2
genCExpr (OBC.Not e)        = UnaryOp BoolNot $ genCExpr e
genCExpr (OBC.Ifte b e1 e2) = Cond (genCExpr b) (genCExpr e1) (genCExpr e2)
genCExpr (OBC.Sym sid)      = Ident sid
genCExpr (OBC.CaseOfCall e f inScopeVars) =
    let e' = genCExpr e
        -- Important to not forget to include the scrutinee itself as an
        -- argument.
        args = e' : map (\ (Ex var) -> Ident $ getName var) inScopeVars
    in Funcall (Ident f) args

caseC :: forall n b . RecEnumerable n b => C.Expr -> V.Vec n C.Stmt -> C.Stmt
caseC scrut = Switch scrut . V.toList . V.zipWith mkCase (enumerate @n @(BFin n b))
    where
    mkCase x branch = C.Case (valRepC x) (seqStmtC [branch,Break])

-- HACK: because there's no way to make stmt. blocks in the C lib.
seqStmtC :: [C.Stmt] -> C.Stmt
seqStmtC stms = If (LitBool True) stms

skipC :: C.Stmt
skipC = Expr $ Cast (TypeName (TypeSpec Void)) (LitInt 0)

genCStmt :: OBC.Stmt p -> C.Stmt
genCStmt (OBC.Let x e) = Expr $ Ident (getName x) .= genCExpr e
genCStmt (OBC.Ass x e) = Expr $ (selfC .-> getName x) .= genCExpr e
genCStmt OBC.Skip = skipC
genCStmt (OBC.Seq s1 s2) = seqStmtC $ map genCStmt [s1, s2]
genCStmt (OBC.Case (scrut :: OBC.Exp p (BFin n b)) branches) =
    let scrut'    = genCExpr scrut
        branches' = fmap genCStmt branches
    in caseC @n @b scrut' branches'
-- classname_reset(self->objname)
genCStmt (OBC.CallReset obj) =
    Expr $ Funcall (Ident (objType obj ++ "_reset")) [Ident "self" .-> getName obj]
genCStmt (OBC.CallStep x obj args) =
    let args'     = map (extract genCExpr) args
        selfDeref = Ident "self" .-> getName obj : args'
        funCall   = Funcall (Ident (objType obj ++ "_step")) selfDeref
    in Expr $ Ident (getName x) .= funCall

genCStmt (OBC.If cond stmts) = If (genCExpr cond) (map genCStmt stmts)
genCStmt (OBC.Return retExp) = Return . Just $ genCExpr retExp

class FromVar b where
    fromVar :: LT a => Var a -> b

instance FromVar FieldDecln where
    fromVar (x :: Var a) = FieldDecln (cType @a) (getName x)

instance FromVar Param where
    fromVar (x :: Var a) = Param (cType @a) (getName x)

instance FromVar Decln where
    fromVar (x :: Var a) = VarDecln Nothing (cType @a) (getName x) Nothing
