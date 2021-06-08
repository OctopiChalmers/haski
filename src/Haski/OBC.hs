{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

module Haski.OBC where

import Data.Coerce (coerce)
import Control.Monad.State.Lazy (State, get, runState, modify)
import qualified Control.Monad.State.Lazy as St
import Data.Foldable (foldrM)
import qualified Data.Map.Strict as M
import Data.Proxy (Proxy(..))
import qualified Data.Set as S

import Haski.Clock (Clock(..), ClockP)
import Haski.Core (Var, RecEnumerable)
import qualified Haski.Core as Core
import Haski.Enum
import Haski.Norm
import Haski.Schedule (CNCA, CEQ, CEQNode, getClock)
import Haski.Type
import Haski.Util
import qualified Haski.Vec as V


newtype Field a = Field {toTup :: (Var a,a)}

data Obj = Obj
    { objName :: Name  -- ^ Name of the instance
    , objType :: Name  -- ^ Name of class
    }

-- | Class (or object "template") definition
data Class p where
    Class :: Name
        -> [Ex Field]  -- ^ Memory initialization
        -> [Obj]       -- ^ Instances
        -> [Stmt p]    -- ^ Reset statement
        -> Step p      -- ^ Step method
        -> Class p

-- | The "step" method
data Step p where
    Step :: LT a
        => [Ex Var]  -- ^ Arguments
        -> Exp p a   -- ^ Result
        -> [Stmt p]  -- ^ Body
        -> Step p

-- | Mapping from function names to function definitions.
type CaseOfDefs p = M.Map String (CaseDef p)

-- | Function definition for handling the logic of a pattern match.
data CaseDef p = forall retTy . (LT retTy) => CaseDef
    { cdRetTy :: Proxy retTy  -- ^ Return type.
    , cdParams :: [Ex Var]     -- ^ Function parameters.
    , cdGlobalScrutName :: Name
    -- ^ The global variable that the scrutinee will immediately
    -- be assigned to at the beginning of the function.
    , cdFieldExps :: M.Map Name (Ex (Exp p))
    -- ^ Variable bindings for expressions corresponding to the fields
    -- of Partition ADTs. For example, a ("var_0", Var "x" :: Exp p Int)
    -- binding is roughly equivalent to the "int var_0 = x;" C statement.
    -- Here, the bound expression is the result of applying
    -- "Haski.Lang.partition" to the field of some constructor. This expression
    -- can be used in multiple locations, so we bind it to a variable to reduce
    -- code that computes the same thing several times.
    , cdBody :: [Stmt p]  -- ^ Function body.
    }

data Stmt p where
    Let     :: LT a => Var a -> Exp p a -> Stmt p
    Ass     :: Var a -> Exp p a -> Stmt p
    Skip    :: Stmt p
    Seq     :: Stmt p -> Stmt p -> Stmt p
    Case    :: (RecEnumerable n b)
        => Exp p (BFin n b)  -- ^ Scrutinee
        -> V.Vec n (Stmt p)
        -> Stmt p
    CallReset   :: Obj -> Stmt p
    CallStep    :: LT a
        => Var a        -- ^ variable bound with result
        -> Obj          -- ^ object instance
        -> [Ex (Exp p)] -- ^ arguments
        -> Stmt p
    If      :: Exp p Bool -> [Stmt p] -> Stmt p  -- "if exp { stmts }"
    Return  :: Exp p a -> Stmt p                 -- "return exp;"

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

    GtPoly :: (LT a, Num a) => Exp p a -> Exp p a -> Exp p Bool
    Not    :: Exp p Bool -> Exp p Bool
    Ifte   :: LT a => Exp p Bool -> Exp p a -> Exp p a -> Exp p a
    Sym    :: ScrutId -> Exp p a
    -- | Function call to a generated pattern matching function.
    CaseOfCall :: (LT a, LT b)
        => Exp p a  -- ^ Scrutinee expression.
        -> String   -- ^ Function name.
        -> [Ex Var] -- ^ Other function arguments. These are variables which
                    -- are expected to be in scope at the call site, but would
                    -- be out of scope in our generated function, so we need
                    -- to explicitly pass them as arguments.
        -> Exp p b

deriving instance Eq (Var a)
deriving instance Ord (Var a)

-- | Most cases are trivial, but the CaseOf constructor needs to check if types
-- of its arguments (that are not the 'b' in return 'Exp p b') are equal too,
-- which is why we cannot derive Eq. A problem with defining equality of GADTs
-- in general.
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

    Not e        == Not e'          = e == e'
    Ifte b e1 e2 == Ifte b' e1' e2' = b == b' && e1 == e1' && e2 == e2'
    Sym s        == Sym s'          = s == s'
    -- Function calls to pattern matching functions are never equal for now
    CaseOfCall{} == CaseOfCall{} = False
    -- Ditto for GtPoly
    GtPoly{}     == GtPoly{}= False

    _ == _ = False

-- These are basically copies of types from "Haski.Core", but contain 'Exp'
-- instead of 'Haski.Core.GExp'.
type ScrutId = String
data Scrut p a = LT a => Scrut (Exp p a) ScrutId
data Branch p t b = LT b => Branch (Exp p Bool) (Exp p b)
deriving instance Eq a => Eq (Scrut p a)
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

data GenSt p = GenSt
    { fields  :: [Ex Field]
    , objs    :: [Obj]
    , reset   :: [Stmt p]
    , seed    :: Seed

    , funDefs :: CaseOfDefs p
    -- ^ Function definitions used to handle pattern matching logic. These are
    -- generated during translation of expressions.

    , fieldExps :: [M.Map Name (Ex (Exp p))]
    -- ^ Stack of expressions, where each expression corresponds to the field of
    -- some Partition ADT. The Name is the assigned variable name generated by
    -- 'Haski.Core.newFieldTagger'. When we translate a NGCaseOf expression with
    -- 'te', we add a new Map onto the stack, creating a new context. When we
    -- "exit" the expression, we pop the map off the stack. Keeping a stack
    -- of mappings allows us to have nested caseof-expressions without scoping
    -- issues.

    , globalVars :: S.Set (Ex Var)
    -- ^ Accumulated variable usage that need to be declared as global variables
    -- in the final C output.
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
te :: forall p a . NGExp p a -> Gen p (Exp p a)
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

te (NGGtPoly _ e1 e2)    = GtPoly <$> te e1 <*> te e2
te (NGNot _ e)           = Not <$> te e
te (NGIfte _ b e1 e2)    = Ifte <$> te b <*> te e1 <*> te e2
te (NGSym _ sid)         = do
    let newVar = Core.MkVar @a (sid, Nothing)
    modify (\s -> s { globalVars = Ex newVar `S.insert` globalVars s })
    pure $ Sym sid
te (NGFieldExp _ name e) = do
    -- When we encounter an expression tagged as a field to a constructor,
    -- we assume that we are currently "inside" a case-of function.
    -- We need to add a binding to the expression to the current context, so
    -- that it can be reused in following code.
    e' <- te e
    modFieldExpsTop (M.insert name (Ex e'))

    -- Also, We must also add the name of the variable to the global variables of the
    -- compilation state, so that we can generate a declaration for it in the
    -- backend (without having to use State in the backend).
    let newVar = Core.MkVar @a (name, Nothing)
    modify (\s -> s { globalVars = Ex newVar `S.insert` globalVars s })

    return $ Sym name

{- (the `te NGCaseOf` case should probably be a separate function...)
== How are CaseOf:s compiled? ==

Recall that a CaseOf holds a scrutinee expression and branches (containing
expressions). To compile a CaseOf, we generate a new function to handle
the pattern matching logic. This function will take the scrutinee as an argument
and its body will contain the branches, compiled to if-statements.

When we translate an NGCaseOf, we only return the __call__ to the pattern
matching function. As for the function definition, we build a 'CaseOfDef'
construct and store it in state; this state is then passed to the appropriate
code generator (such as Haski.Backend.C), along with the rest of the program.

Once in the code generator, we can simply translate the CaseOfDefs into
C functions separately. The only problem is that, because we create a separate
function to handle the logic, we might be using variables that were in scope
in our Haskell expression, but are now out of scope since they are only visible
in the body of the caller of our pattern matching function.

To handle this problem, we need to keep track of all variables used in the
body of our pattern matching function, so we can pass them explicitly as
arguments. We can do this while building our CaseOfDefs; this is why
'newCaseDef' returns the function name, the CaseDef, AND a list of (Ex Vars).
This list of variables is stored in both the CaseOfDefs (for the function
signature), and the function call expression (so we can supply the right
arguments when calling).

To keep field expressions in scope, we use global variables (à la hpatterns).
This is only because I didn't have enough time to pass these via the function
calls properly (nested caseof calls needs some more sophisticated context
management than what I have hacked together here).

Field expressions are, unfortunately, calculated and assigned for every caseof
function they are used in, even if they could have re-used one from their
parent. This is potentially redundant and inefficient, in particular if the
operation in 'partition' is expensive, but it is done this way because it is
hard to correctly only generate the field expression calculation and assignment
only once, where it is needed (for example, in the same function whose scrutinee
it is derived from). This is just due to my shoddy scoping management; it's
probably easier to fix this if re-done from scratch.

--

This is noted in the Haski.Backend.C module description as well, but it should
be noted that this method of keeping variables in scope is not very robust;
we assume that everything we can use in our Haskell expression will also be
in scope in the generated C code. Currently, I think this is the case;
all variables we can reference will be declared and in scope in the body of
the "xxx_step" function. If a change in implementation causes this to change
however, the generated C code could posibly contain undeclared/undefined/etc
variables.
-}
te (NGCaseOf
    _
    (scrut    :: Core.Scrut (p, NormP) scrutTy)
    (branches :: [Core.Branch (p, NormP) retTy]))
    = do
        -- Translate the scrutinee expression, which will be the argument to the
        -- call to the pattern matching function.
        let Core.Scrut e sid = scrut
        e' <- te e

        -- Generate the definition of the pattern matching function and add
        -- it to the compilation state. While generating the function defintion,
        -- we also get a list of used variables that would become unbound in
        -- the generated functions (in the new scope); we need to explicitly
        -- create parameters for these in the generated function.
        (funName, def, inScopeVars) <- newCaseDef sid branches
        modify $ \ st -> st { funDefs = M.insert funName def (funDefs st) }


        pure $ CaseOfCall e' funName inScopeVars
  where
    newCaseDef :: ScrutId -> [Core.Branch (p, NormP) b] -> Gen p (String, CaseDef p, [Ex Var])
    newCaseDef sid bs = do
        -- Since we are "entering" a new (case-of) function, we need to open
        -- a new context, since any encountered FieldExps belong to __this__
        -- function definition in particular.
        pushFieldExps

        (ifs, vars) <- unzip <$> mapM mkIf bs
        let inScopeVars = S.elems (S.unions vars)

        -- The scrutinee parameter of the function must use the same name
        -- as the references to it inside the function, generated when applying
        -- 'Haski.Lang.caseof'.
        funName <- freshName "case_of_"
        let scrutParam = Core.MkVar @scrutTy (Core.scrutineeParamName, Nothing)

        -- Retrieve the encountered FieldExps in this function definition and
        -- remove the top context from the stack since we are now "exiting"
        -- the function.
        fieldExps <- popFieldExps

        let caseDef = CaseDef
                { cdRetTy = Proxy @retTy
                , cdParams = Ex scrutParam : inScopeVars
                , cdGlobalScrutName = sid
                , cdFieldExps = fieldExps
                , cdBody = ifs
                }

        return (funName, caseDef, inScopeVars)

    -- Create an if-statement corresponding to one branch of a pattern match.
    -- Return the statement and all variables contained within the body.
    mkIf :: Core.Branch (p, NormP) b -> Gen p (Stmt p, S.Set (Ex Var))
    mkIf (Core.Branch cond body) = do
        -- Find all variables used inside the function body so we can provide
        -- the caller with the correct arguments.
        let vars = collect body `S.union` collect cond
        cond' <- te cond
        body' <- te body
        pure (If cond' [Return body'], vars)

    -- Traverse an expression tree and return any variables we encounter.
    collect :: forall p b . LT b => NGExp p b -> S.Set (Ex Var)
    collect = go S.empty
      where
        go :: LT c => S.Set (Ex Var) -> NGExp p c -> S.Set (Ex Var)
        go vars = \case
            (NGVal _ x) -> vars
            (NGVar _ x) -> Ex x `S.insert` vars
            (NGWhn _ e _xc) -> go vars e
            (NGAdd _ e1 e2) -> go (go vars e1) e2
            (NGMul _ e1 e2) -> go (go vars e1) e2
            (NGSig _ e)     -> go vars e
            (NGNeg _ e)     -> go vars e
            (NGAbs _ e)     -> go vars e
            (NGGt _ e1 e2)  -> go (go vars e1) e2
            (NGGtPoly _ e1 e2) -> go (go vars e1) e2
            (NGNot _ e)        -> go vars e
            (NGIfte _ b e1 e2) -> go (go (go vars b) e1) e2
            (NGSym _ _sid)      -> vars
            (NGFieldExp _ _name e) -> go vars e

            (NGCaseOf _ (Core.Scrut e _sid) branches) ->
                go vars e `S.union` S.unions (map goBranch branches)
              where
                goBranch (Core.Branch b e) = collect b `S.union` collect e

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

-- Stuff needed to generate code for pattern matching functions.
data CaseOfInfo p = CaseOfInfo (CaseOfDefs (p, ClockP)) [Ex Var]

tpN :: CEQNode p -> Seed -> ((CClass p, CaseOfInfo p), Seed)
tpN (EQNode name args eqs res) sd = ((clas, caseOfInfo), seed resSt)
    where
        -- build translation computation
        transM = (,) <$> teqlist eqs <*> te res
        -- execute translation
        ((stmts,res'),resSt) = runState transM (GenSt [] [] [] sd M.empty [] S.empty)
        -- build step method
        step = Step args res' stmts
        -- build class
        clas = Class name
                    (fields resSt) (objs resSt)
                    (reset resSt) step

        caseOfInfo = CaseOfInfo (funDefs resSt) (S.toAscList . globalVars $ resSt)

-- Main entry point
translateNode :: CEQNode p -> Seed -> ((CClass p, CaseOfInfo p), Seed)
translateNode = tpN

localVars :: [Stmt p] -> [Ex Var]
localVars = reverse . S.toList . foldr collect S.empty
    where
    collect (Let x _)        acc = Ex x `S.insert` acc
    collect (CallStep x _ _) acc = Ex x `S.insert` acc
    collect (Seq s1 s2)      acc = collect s1 (collect s2 acc)
    collect (Case _ bs)      acc = foldr collect acc bs
    collect _                acc = acc

--
-- Helper functions for modifying the 'fieldExps' stack
--

-- | Remove the top mapping from the stack of FieldExp mappings and return
-- the mapping.
popFieldExps :: Gen p (M.Map Name (Ex (Exp p)))
popFieldExps = St.gets fieldExps >>= \case
    []       -> error "popFieldsExps: empty stack"
    (x : xs) -> St.modify (\st -> st { fieldExps = xs }) >> return x

-- | Add an empty mapping to the top of the stack of FieldExp mappings.
pushFieldExps :: Gen p ()
pushFieldExps = St.modify (\st -> st { fieldExps = M.empty : fieldExps st })

-- | Apply a function to the top mapping of the stack of FieldExp mappings.
modFieldExpsTop ::
       (M.Map Name (Ex (Exp p)) -> M.Map Name (Ex (Exp p)))
    -> Gen p ()
modFieldExpsTop f = St.gets fieldExps >>= \case
    []       -> error "modFieldExpsTop: empty stack"
    (x : xs) -> St.modify (\st -> st { fieldExps = f x : xs })
