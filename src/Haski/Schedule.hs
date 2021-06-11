{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Haski.Schedule where

import Prelude hiding (reads)
import Haski.Util
import Haski.Type
import Haski.Core
import Haski.Clock
import Haski.Norm
import Haski.Pass

import qualified Data.Set as S
import Data.Graph
import Data.Maybe (listToMaybe)
import Control.Monad.State

import Data.Array (assocs)

-- clocked and normalized expressions/equations
type CNGExp  p  = NGExp (p, ClockP) -- ~ GExp (p , ClockP, NormP)
type CNCA    p  = NCA (p,ClockP)
type CEQ     p  = EQ (p, ClockP)
type CEQNode p  = EQNode (p, ClockP)

getClock :: forall p a . CNGExp p a -> Clock
getClock = getAnn   -- extract clock from `GExp ClockP a`
    . snd           -- discard result of p
    . unpack @p @ClockP
    . fst           -- discard result of NormP
    . unpack @(p,ClockP) @NormP

-- variables read by an NA expression
left :: CNGExp p a -> S.Set Name
left e = vars (getClock e) `S.union` go e
    where
    go :: NGExp p a -> S.Set Name
    go (NGVal _ _)       = S.empty
    go (NGVar _ x)       = S.singleton (getName x)
    go (NGWhn _ e (x,c)) = S.insert (getName x) (go e)
    go (NGAdd _ e1 e2)   = S.union (go e1) (go e2)
    go (NGMul _ e1 e2)   = S.union (go e1) (go e2)
    go (NGAbs _ e)       = go e
    go (NGSig _ e)       = go e
    go (NGNeg _ e)       = go e
    go (NGGt _ e1 e2)    = S.union (go e1) (go e2)

    -- I have no idea if these are right; just threading 'go' through all
    -- sub-expressions. I've left out the implementation for the other
    -- primitives that weren't part of the pattern matching implementation
    -- (NGNot, NGIfte, NGGtPoly).
    go (NGSym _ x) = S.singleton x
    go (NGFieldExp _ _ e) = go e
    go (NGCaseOf _ (Scrut e _) branches) =
        go e `S.union` foldMap goBranch branches
      where
        goScrut (Scrut e _) = go e
        goBranch (Branch condE bodyE) = go condE `S.union` go bodyE

-- variables read the by an NCA expression
leftNCA :: CNCA p a -> S.Set Name
leftNCA (NExp e)       = left e
leftNCA (NMrg ann x m) = S.insert (getName x)
    -- collect names from all branches
    (foldr collect S.empty m)
    where
        collect nca acc = leftNCA nca `S.union` acc

-- variables read by the body of an equation
leftEQ :: CEQ p -> S.Set Name
leftEQ (LetEq _ e)     = leftNCA e
leftEQ (FbyEq _ _ _ e) = left e
leftEQ (AppEq _ _ es)  = foldr collect S.empty es
    where
    collect exExp acc = (extract left exExp) `S.union` acc

-- variables that a clock depends on
vars :: Clock -> S.Set Name
vars Base = S.empty
vars (On ck c x) = S.insert (getName x) (vars ck)

-- variables whose values are defined (but not later modified) by an equation
defines :: CEQ p -> S.Set Name
defines (LetEq x _) = S.singleton $ getName x
defines (FbyEq _ _ _ _) = S.empty
defines (AppEq x _ _) = S.singleton $ getName x

-- variables whose value is modified by an equation
modifies :: CEQ p -> S.Set Name
modifies (LetEq _ _) = S.empty
modifies (FbyEq _ x _ _) = S.singleton (getName x)
modifies (AppEq _ _ _) = S.empty

reads = leftEQ

dependsOn :: CEQ p -> CEQ p -> Bool
dependsOn e1 e2 = not $ S.disjoint (reads e1) (defines e2)
-- note: disjoint <==> intersection is empty

antiDependsOn :: CEQ p -> CEQ p -> Bool
antiDependsOn e1 e2 = not $ S.disjoint (modifies e1) (reads e2)

-- Adjacency list of equations as nodes
type AdjList p = [(CEQ p     -- node (i.e., the paylod)
    , Int
    , [Int])]

mkAdjList :: [CEQ p] -> (CEQ p -> CEQ p -> Bool) -> AdjList p
mkAdjList eqs hasEdgeTo = [ (eq,v,neighbors eq)
    | (eq,v) <- eqVertPairs ]
    where
        -- [(eq1,0),(eq2,1),(eq3,2),..]
        eqVertPairs = zip eqs [0..]
        -- neighbouring *vertices* of eq
        neighbors eqX = [ vY
            | (eqY,vY) <- eqVertPairs
            , eqX `hasEdgeTo` eqY ]

-- assumes that both lists have the same equations
unionAdjList :: AdjList p -> AdjList p -> AdjList p
unionAdjList l1 l2 = [ (eq1,v1,ns1 ++ ns2)
    | (eq1,v1,ns1) <- l1
    , (_,v2,ns2) <- l2
    , v1 == v2 ]

type Sched = State Int

instance Plant Int Int where
    plant = put

instance Fresh Int where
    getSeed = get

-- Shamelessly copied from https://stackoverflow.com/questions/8935323/detecting-cycles-of-a-graphmaybe-directed-or-undirected-in-haskell
-- | Calculates all the nodes that are part of cycles in a graph.
cyclicVertex :: Graph -> Maybe (Vertex)
cyclicVertex graph =
  listToMaybe . map fst . filter isCyclicAssoc . assocs $ graph
  where
    isCyclicAssoc = uncurry $ reachableFromAny graph
    -- | In the specified graph, can the specified node be reached, starting out
    -- from any of the specified vertices?
    reachableFromAny :: Graph -> Vertex -> [Vertex] -> Bool
    reachableFromAny graph node =
        elem node . concatMap (reachable graph)

-- "untangle" SCC created by anti-dependencies
untangle :: (AllEq p q) => SCC (CEQ p) -> Sched [CEQ p]
untangle (AcyclicSCC eq) = return [ eq ]
untangle (CyclicSCC eqs) = concat <$> mapM repairEq eqs
    where
    -- repair a tangled fby-eq by creating a copy variable
    repairEq (FbyEq ann x v e) = do
        copyVar <- fresh
        return [ LetEq copyVar (NExp e)
                , FbyEq ann x v (NGVar ann copyVar) ]
    repairEq _   = error "Scheduling error: will not add copy var to non-fby equation."

scheduleEqs :: (AllEq p q) => [CEQ p] -> Sched [CEQ p]
scheduleEqs eqs =
    case depCycle of
        Nothing -> do
            let antiDepKnots = stronglyConnComp schedList
            concat <$> mapM untangle antiDepKnots
        (Just _) -> error "Scheduling error: found a dependency cycle, get your shit together!"
    where
        -- make dep graph
        depList        = mkAdjList eqs dependsOn
        (depGraph,_,_) = graphFromEdges depList

        -- find dependency cycle (of vertices! not nodes)
        -- Note: could be disabled for the sake of performance
        --  since "in practice", this graph may not have cycles.
        --  This is because Haskell enforces scoping when building equations
        --  and normalization maybe careful enough to preserve scoping (verify!)
        depCycle = cyclicVertex depGraph

        -- build list for scheduling by extending with anti-deps
        antiDepList = mkAdjList eqs antiDependsOn
        schedList   = depList `unionAdjList` antiDepList

scheduleN :: (AllEq p q) => (CEQNode p) -> Sched (CEQNode p)
scheduleN (EQNode name args eqs res) = do
    eqs' <- scheduleEqs eqs
    return (EQNode name args eqs' res)

scheduleNode :: (AllEq p q) => CEQNode p -> Seed -> (CEQNode p,Seed)
scheduleNode n = runState (scheduleN n)
