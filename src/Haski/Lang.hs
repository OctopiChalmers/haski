{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Haski.Lang (
    -- Basic Combinators
    val
    , fby
    , when
    , merge
    , match
    , ifte
    , mapE
    , letDef
    , node
    , gtE

    -- Types and Constraints
    , Stream
    , LT(..)
    , Int8
    , FinEnum
    , Haski
    , Arg
    , Res
    , Box
    , BEnum(..)
    , TypeRepLT
    , userDefLT

    -- Pattern matching
    , Partition (..)
    , caseof

    -- IFC extension
    , LStream
    , labelOf
    , label
    , unlabel
    , toLabeled
    , getLabel
    , runAs

    -- Compilation
    , compile
) where

import Prelude hiding ((<>))
import Data.Int (Int8)
import Data.Maybe (fromJust)
import qualified Data.Map as M
import Data.Constraint (withDict)
import Data.Typeable (Typeable)
import Control.Monad (replicateM,unless)
import qualified Control.Monad as ControlM
import Control.Monad.Identity (Identity, runIdentity)
import Control.Monad.State.Lazy (StateT, get, runState, execState, modify)
import GHC.TypeLits
import GHC.Records

import Haski.Enum hiding (not)
import Haski.Type
import Haski.Core hiding (Def, Let)
import qualified Haski.Core as Core
import Haski.Fin (valRep)
import qualified Haski.Vec as V
import Haski.Pretty
import Haski.Util
import Haski.Norm (normNode)
import Haski.Clock (clockNode)
import Haski.Schedule (scheduleNode)
import Haski.OBC (translateNode)
import Haski.Backend (compileClasses)
import Haski.Backend.C ()
import qualified Language.C99.AST as C (TransUnit)
import Haski.Pass (AllEq,RawP)
import Haski.DCLabel.Core
import Haski.DCLabel.NanoEDSL (newDC)
import Haski.DCLabel.PrettyShow

import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (prettyShow)


----------------------------
-- Pattern matching stuff --
----------------------------

class Partition a t where
    -- TODO: from 't' to 'Haski t'
    partition :: [Stream a -> (Stream Bool, t)]

-- TODO: Currently lacks
-- * Unique variable generation (so we can have nested cases if necessary)
-- * The stuff to avoid redundant output code when referencing pattern
--   variables multiple times (leading to the expressions returned by
--   'partition' appearing multiple times as well.)
caseof :: forall t a b . (Partition a t, LT a, LT b, Typeable t)
    => Stream a
    -> (t -> Stream b)
    -> Haski (Stream b)
caseof scrut f = do
    -- TODO Merge usage of exiting GVar so we can freeride on its clock
    -- inference implementaiton (same for Norm etc.)
    scrutId <- freshName "SCRUTID"
    -- let scrutVar = Var $ MkVar (scrutId, Nothing)
    let scrutVar = Sym scrutId
    let branches = map ($ scrutVar) (partition @a @t)
    pure $ CaseOf (Scrut scrut scrutId) (map mkBranch branches)
  where
    mkBranch :: (Stream Bool, t) -> Branch RawP b
    mkBranch (pred, t) = Branch pred (f t)

----------------------------------
-- Primitive Lustre combinators --
----------------------------------

-- | Insert a value.
val :: (LT a) => a -> Stream a
val = Val

-- | Followed-by combinator for defining recursive streams.
fby :: (LT a) => a -> Stream a -> Haski (Stream a)
fby x e = letDef (Fby x e)

-- | Sampling combinator for projecting streams.
when :: forall a b . (FinEnum b)
    => Stream a -> (Stream b , b) -> Stream a
when e (s,x) = withLTa $ withLTb $
    When e (cast (toVar s), toBFin @b x)
    where
        withLTa = withDict (getLTDict e)
        withLTb = withDict (getLTDict s)

-- | Sampling combinator for combining streams.
merge :: forall a b . (FinEnum a) =>
    (Stream a) -> (a -> Stream b) -> Stream b
merge x f = withLTa $
    let
        bs :: V.Vec (Size a) (Stream b)
        bs = theTrick f
        withLTb = withDict (getLTDict (V.head bs))
    in withLTb $ Merge (cast (toVar x)) (theTrick f)
    where
        withLTa = withDict (getLTDict x)

-- | Greater-than, as a primitive.
gtE :: Stream Int-> Stream Int -> Stream Bool
gtE e1 e2 = Gt e1 e2

-----------------------
-- Derived operators --
-----------------------

-- | `match` combinator for pattern-matching on streams.
class Streams b where
    match :: (LT a, FinEnum a) =>
        (Stream a) -> (a -> b) -> Haski b

matchExp :: forall a b . (LT a, LT b, FinEnum a) =>
    (Stream a) -> (a -> Stream b) -> Stream b
matchExp x f =
    let body = theTrick f
        whens = theTrick $ \ a -> flip (when @b) (x,a)
    in Merge (cast (toVar x)) (V.zipWith ($) whens body)

instance LT b => Streams (Stream b) where
    match x f = letDef (matchExp x f)

instance (Streams b, Streams c) => Streams (b,c) where
    match x f = do
        p <- match x (fst . f)
        q <- match x (snd . f)
        return (p,q)

-- NOTE: This instance expects the programmer to obey
--  an invariant that each branch of the `match` invocation
--  returns a list of the same size. However, this
--  isn't enforced, and the invocation may well fail. ¯\_(ツ)_/¯
--  The expected behavior of, for example, an invocation that
--  returns a list of stream expressions, is that it defines a
--  `Merge` equation for each element of the list.
instance Streams b => Streams [b] where
    match x f = do
        -- we use the first branch as size indicator (`sizeInd`)
        -- to identity the number of streams to be defined in each branch.
        let sizeInd = V.head (theTrick f)
        if (null sizeInd)
        -- base case (no streams to be defined)
        then return []
        -- inductive case
        else do
            -- define the stream for the head element of the list
            p <- match x (head . f)
            -- define streams for the remaining list
            qs <- match x (tail . f)
            return (p : qs)

ifte :: (LT a) => Stream Bool -> Stream a -> Stream a -> Stream a
ifte cond th el = matchExp cond $ \x -> if x then th else el

mapE :: (LT a, LT b, FinEnum a) => (a -> b) -> Stream a -> Stream b
mapE f e = matchExp e (val . f)

-------------------------
-- Security primitives --
-------------------------

type Label = DCLabel

data LStream a = LStreamTCB {
    getLabelTCB :: Label
    , getExpTCB :: Stream a}

-- | Get the current (floating) label.
getLabel :: Haski (Label)
getLabel = lcur <$> get

-- | Query label of a labeled stream.
labelOf :: LStream a -> Haski (Label)
labelOf = return . getLabelTCB

-- | Label a stream.
label :: Label -> Stream a -> Haski (LStream a)
label l e = do
    lc <- getLabel
    unless (lc `canflowto` l)
        (illFlow $ "IFC label violation: "
            ++ showL lc ++ " doesn't flow to " ++ showL l)
    return (LStreamTCB l e)
    where
    showL :: Label -> String
    showL l = show (prettyShow l)

-- | Unlabel a stream.
unlabel :: LStream a -> Haski (Stream a)
unlabel e = do
    lc <- getLabel
    let lc' = lc `join` (getLabelTCB e)
    plant @St @Label lc'
    return $ getExpTCB e

-- | Build a secure computation without getting tainted.
toLabeled :: Haski (Stream a) -> Haski (LStream a)
toLabeled m = do
    lc <- getLabel
    res <- m
    lc' <- getLabel
    res' <- label lc' res
    plant @St @Label lc
    return res'

-- | Run a Haski computation which produces an observable result.
class IsStream f where
    runAs :: Haski (f a) -> Principal -> Haski (Stream a,Label)

instance IsStream Stream where
    runAs prog princ = do
        res <- toLabeled $ do
            plant @St @Label (newDC princ princ)
            prog
        return (getExpTCB res,getLabelTCB res)

instance IsStream LStream where
    runAs prog princ = do
        runAs (prog >>= unlabel) princ

-- utlity (not exposed)
illFlow :: String -> Haski ()
illFlow = fail

---------------------------
-- Haski monad internals --
---------------------------

-- State underlying the monad
data St = MkSt { next :: Seed
    , stmts :: [Def]    -- list of definitions
    , lcur  :: Label    -- current / floating label
    }

-- Statements
data Def where
    Let :: LT a => Var a -> Stream a -> Def
    Arg :: LT a => Name -> Var a -> Stream a -> Def
    Res :: LT a => Name -> Var a -> Stream a -> Def
    -- Res marks a result (which may be any expression) with a special result variable

-- | Monad that collects list of statements and maintains a variable seed
type Haski = StateT St Identity

-- | Letine a variable, no need to give a name!
letDef :: forall a . LT a => Stream a -> Haski (Stream a)
letDef e = do
  var <- fresh
  addDef (Let var e)
  return (Var var)

rootLabel = newDC emptyComponent allComponent

-- | Run the monad and extract list of statements.
runHaski :: Seed -> Haski (Stream a) -> (Stream a, [Def], Seed)
runHaski seed m = let
    (e,MkSt seed' stmts _) = runState m (MkSt seed [] rootLabel)
    in (e, reverse stmts, seed')

------------------
-- Boxing Nodes --
------------------

-- register a node argument
class Arg a where
    arg :: Name -> a -> Haski a

-- register a node result
class Res b where
    res :: Name -> b -> Haski b

-- register an expression argument
instance LT a => Arg (Stream a) where
    arg name exp = do
        x <- fresh
        addDef (Arg name x exp)
        return (Var x)

-- register an expression argument
instance LT a => Arg (LStream a) where
    arg name lexp = do
        x <- arg name (getExpTCB lexp)
        return (LStreamTCB (getLabelTCB lexp) x)

-- register a pair of arguments
instance (Arg a, Arg b) => Arg (a , b) where
    arg name (x , y) = do
        x' <- arg name x
        y' <- arg name y
        return (x',y')

-- register an Streamression result
instance LT a => Res (Stream a) where
    res name exp = do
        x <- fresh
        addDef (Res name x exp)
        return (Var x)

-- register an expression result
instance LT a => Res (LStream a) where
    res name lexp = do
        x <- res name (getExpTCB lexp)
        return (LStreamTCB (getLabelTCB lexp) x)

-- box a function
class Box b where
    box :: Arg a => Name -> (a -> b) -> (a -> b)

-- box a function whose argument can be registered and result can be boxed
instance (Arg b, Box c) => Box (b -> c) where
    box name f = curry (box name (uncurry f))

-- box a monad whose result can be registered
instance (Res b) => Box (Haski b) where
    box name f = \ e -> do
        x' <- arg name e
        r <- f x'
        r' <- res name r
        return r'

-- | Names a node (synonym to box).
node :: (Arg a, Box b) => Name -> (a -> b) -> (a -> b)
node = box

------------------
-- Parsing Defs --
------------------

-- build a node from statements
mkNode :: [Def] -> [Def] -> Def -> Node
mkNode args defs (Res name _ e) = GNode name nArgs nBody e
    where
        nArgs = [Ex x | (Arg _ x _) <- args]
        -- prep body
        nBody = [Core.Let x e | (Let x e) <- defs]

-- build a node call from statements
mkNodeApp :: [Def] -> Def -> Core.Def
mkNodeApp args (Res name x _) = App x name nArgs
    where
        nArgs = [Ex e | (Arg _ _ e) <- args]

isLet (Let _ _) = True
isLet _         = False

isArg (Arg _ _ _) = True
isArg _           = False

isRes (Res _ _ _)   = True
isRes _           = False

-- I: [Let, Let, Arg, Let, Res, ...]
-- O: ([Let, Let], [Arg, Let, Res, ...])
parseLets :: [Def] -> ([Def],[Def])
parseLets = span isLet

-- I: [Arg, Arg, Let, Res, ...]
-- O: ([Arg, Arg], [Let, Res, ...])
parseArgs :: [Def] -> ([Def],[Def])
parseArgs = span isArg

-- parseRes([Res, Let, ...]) == (Res,[Let, ...])
-- parseRes ([Res, Res, ...]) == \bot
-- parseRes ([Let/Arg, ...]) == \bot
parseRes :: [Def] -> (Def,[Def])
parseRes stmts = let ([x],y) = span isRes stmts in (x,y)

dropLets :: [Def] -> [Def]
dropLets = snd . parseLets

readNodeCall :: [Def]
    -> ([Def]      -- Args
        , [Def]    -- Lets
        , Def      -- Result
        , [Def])   -- Remaining statements
readNodeCall stmts = (args,defs,res,remDefs)
    where
        (args,stmtsSansArgs) = parseArgs stmts
        (defs,stmtsSansLets) = parseLets stmtsSansArgs
        (res,remDefs) = parseRes stmtsSansLets

addLet = consTo defs

-- parse a single node
parseNode :: [Def] -> ParseM [Def]
parseNode stmts = do
    -- register node call
    addLet call
    -- are we parsing a new node?
    nodeMap <- nodeMap <$> get
    let isNewNode = M.notMember name nodeMap
    -- if yes, register
    ControlM.when isNewNode (plant $ M.insert name node nodeMap)
    -- take your remains and GTHO
    return remDefs
    where
        -- break down input into args, defs, result and remains
        (args,defs,res@(Res name _ _),remDefs) = readNodeCall stmts
        -- build node
        node  = mkNode args defs res
        -- build a call to node
        call  = mkNodeApp args res

data PSt = PSt {defs :: [Core.Def], nodeMap :: M.Map Name Node}
type ParseM a = StateT PSt Identity a

instance Plant PSt [Core.Def] where
    plant ds = modify $ \st -> st {defs = ds}

instance Plant PSt (M.Map Name Node) where
    plant m = modify $ \st -> st {nodeMap = m}

compileDefs :: [Def] -> ([Core.Def],[Node])
compileDefs stmts = let pst = execState (go stmts) (PSt [] M.empty)
    in (reverse . defs $ pst, map snd . M.toList . nodeMap $ pst)
    where
    go :: [Def] -> ParseM ()
    go stmts = do
        mapM addLet [ Core.Let x e | (Let x e) <- strayLets ]
        ControlM.when (not . null $ stmts') (parseNode stmts' >>= go)
        where
        (strayLets,stmts') = parseLets stmts

haskiMToNodes :: LT a => Seed -> Haski (Stream a) -> ([Node],Seed)
haskiMToNodes seed m = (nodes ++ [packMain defs res], seed')
    where
    -- run the monad to get statements
    (res,stms,seed') = runHaski seed m
    -- compile the statements
    (defs,nodes) = compileDefs stms
    -- utlity to pack a main node
    packMain :: LT a => [Core.Def] -> Stream a -> Node
    packMain ds = GNode "main" [] ds

compile :: LT a => Haski (Stream a) -> IO ()
compile m = print . pPrint $ cUnit
    where
    -- BEGIN compilation
    -- parse
    (ns,s1)   = haskiMToNodes 0 m
    -- clock-check
    ns_c      = map clockNode ns
    -- normalize
    (ns_n,s2) = runPass normNode s1 ns_c
    -- schedule
    (ns_s,s3) = runPass scheduleNode s2 ns_n
    -- translate to classes
    (cs,s4)   = runPass translateNode s3 ns_s
    -- END compilation
    cUnit     = compileClasses @C.TransUnit cs
    -- utlities
    runPass :: (a -> Seed -> (b,Seed)) -- | pass
        -> Seed         -- | seed
        -> [a]          -- | pass arguments
        -> ([b],Seed)   -- | pass results and a residue seed
    runPass f si ns_i = foldr (go f) ([],si) ns_i
        where
        go f n (ns,s) = let (n',s') = f n s
            in (n':ns,s')

-----------------
-- Boilerplate --
-----------------

instance Plant St Seed where
    plant seed = modify $ \ st -> st {next = seed}

instance Plant St [Def] where
    plant stmts = modify $ \ st -> st {stmts = stmts}

instance Plant St Label where
    plant lbl = modify $ \ st -> st {lcur = lbl}

addDef :: Def -> Haski ()
addDef = consTo stmts

instance Show Def where
    show = show.pPrint

instance {-# OVERLAPPING #-} Show [Def] where
    show = show . pPrint

instance Pretty Def where
    pPrint (Let x e) = text "Let"
        <+> text (getName x)
        <+> equals
        <+> pPrint e
    pPrint (Arg n x e) = text "Arg"
        <+> lparen <> text n <> rparen
        <+> text (getName x)
        <+> pPrint e
    pPrint (Res n x e) = text "Result"
        <+> lparen <> text n <> rparen
        <+> text (getName x)
        <+> pPrint e

instance {-# OVERLAPPING #-} Pretty [Def] where
    pPrint ss = foldr (\s acc -> (pPrint s) $$ acc) empty ss

instance (LT a, Num a) => Num (Haski (Stream a)) where
    e1 + e2  = Add <$> e1 <*> e2
    e1 * e2  = Mul <$> e1 <*> e2
    abs e    = Abs <$> e
    signum e = Sig <$> e
    fromInteger e = Val <$> return (fromInteger e)
    negate e = Neg <$> e

toVar :: Stream a -> Var a
toVar (Var v) = v
toVar e       = error $ "Sampled expression " ++ show (pPrint e)
    ++ " (in merge/when) must be pre-defined as an equation"

instance Fresh St where
    getSeed = next <$> get
