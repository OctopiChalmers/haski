{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702) && (__GLASGOW_HASKELL__ < 704)
{-# LANGUAGE SafeImports #-}
#endif
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 704)
{-# LANGUAGE Unsafe #-}
#endif
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-|
This module implements Disjunction Category Labels.

A DCLabel is a pair of 'secrecy' and 'integrity' category sets or
components, of type 'Component'. Each component is simply a set of
clauses in propositional logic (without negation).  A component
can either correspond to the term 'MkComponentAll', representing
falsehood, or a set of categories (clauses): (of type 'Conj')
corresponding to the conjunction of ategories (of type 'Disj').
Each category, in turn, is a disjunction of 'Principal's, where
a 'Principal' is just a 'ByteString' whose meaning is up to the
application.

A category imposes an information flow restriction. In the case of
secrecy, a category restricts who can read, receive, or propagate
the information, while in the case of integrity it restricts who
can modify a piece of data. The principals constructing a category
are said to /own/ the category.

For information to flow from a source labeled @L_1@ to a sink @L_2@, the
restrictions imposed by the categories of @L_2@ must at least as restrictive as
all the restrictions imposed by the categories of @L_1@ (hence the conjunction)
in the case of secrecy, and at least as permissive in the case of integrity.
More specifically, for information to flow from @L_1@ to @L_2@, the labels
must satisfy the \"can-flow-to\" relation: @L_1 &#8849; L_2@.  The &#8849;
label check is implemented by the 'canflowto' function.  For labels
@L_1=\<S_1, I_1\>@, @L_2=\<S_2, I_2\>@ the can-flow-to relation is satisfied
if the secrecy category set @S_2@ 'implies' @S_1@ and @I_1@ 'implies' @I_2@
(recall that a category set is a conjunction of disjunctions of principals).
For example, @\<{[P_1 &#8897; P_2]},{}\> &#8849; \<{[P_1]},{}\>@ because data
that can be read by @P_1@ is more restricting than that readable by @P_1@
or @P_2@. Conversely, @\<{{},[P_1]}\> &#8849; \<{},[P_1 &#8897; P_2]},{}\>@
because data vouched for by @P_1@ or @P_2@ is more permissive than just @P_1@
(note the same idea holds when writing to sinks with such labeling).

A piece of a code running with a privilege object (of type 'TCBPriv'), i.e.,
owning a 'Principal' confers the right to modify labels by removing any
'secrecy' categories containing that 'Principal' and adding any 'integrity'
categories containing the 'Principal' (hence the name disjunction categories:
the category @[P1 &#8897; P2]@ can be /downgraded/ by either 'Principal'
@P1@ or @P2@).  More specifically, privileges can be used to bypass
information flow restrictions by using the more permissive \"can-flow-to given
permission\" relation:&#8849;&#7528;. The label check function implementing
this restriction is 'canflowto_p', taking an additional argument (of type
'TCBPriv'). For example, if @L_1=\<{[P_1 &#8897; P_2] &#8896; [P_3]},{}\>@,
and @L_2=\<{[P_1]},{}\>@, then @L_1 &#8930; L_2@, but given a privilege
object corresponding to @[P_3]@ the @L_1 &#8849;&#7528; L_2@ holds.

To construct DC labels and privilege objects the constructors exported by
this module may be used, but we strongly suggest using "DCLabel.NanoEDSL"
as exported by "DCLabel.TCB" and "DCLabel.Safe". The former is to be used by
trusted code only, while the latter module should be imported by untrusted
code as it prevents the creation of arbitrary privileges.

-}

module Haski.DCLabel.Core ( -- * Components
    Disj(..), Conj(..), Component(..)
    , emptyComponent, allComponent
    , Lattice(..)
    , ToLNF(..)
    -- ** DC Components
    , DCLabel(..)
        -- * Principals
    , Principal(..), CreatePrincipal(..)
    -- * Privileges
    -- $privs
    , TCBPriv(..), Priv
    , RelaxedLattice(..)
    , noPriv, rootPrivTCB
    , delegatePriv, createPrivTCB
    , CanDelegate(..), Owns(..)
        -- * Component/internal operations
    , and_component, or_component, cleanComponent, implies
    , DisjToFromList(..)
    , listToComponent, componentToList
) where


#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
import safe Data.List (nub, sort, (\\))
import safe Data.Maybe (fromJust)
import safe Data.Monoid
import safe Data.Functor ((<$>))
#else
import Data.List (nub, sort, (\\))
import Data.Maybe (fromJust)
import Data.Monoid
import safe Data.Functor ((<$>))
#endif

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8 as C
import Data.Serialize

--
-- Categories
--

-- | A category, i.e., disjunction, of 'Principal's.
-- The empty list '[]' corresponds to the disjunction of all principals.
-- Conceptually, @[] =  [P_1 &#8897;  P_2 &#8897; ...]@
newtype Disj = MkDisj { disj :: [Principal] }
        deriving (Eq, Ord, Show, Read)


-- | A category set, i.e., a conjunction of disjunctions.
-- The empty list '[]' corresponds to the single disjunction of all principals.
-- In other words, conceptually, @[] =  {[P_1 &#8897; P_2 &#8897; ...]}@
-- Logically '[]' = @True@.
newtype Conj = MkConj { conj :: [Disj] }
        deriving (Eq, Ord, Show, Read)

--
-- Components
--

{- $labels
   A component is a conjunction of disjunctions of principals. A
   'DCLabel' is simply a pair of such components. Hence, we define
   almost all operations in terms of this construct, from which the
   'DCLabel' implementation follows almost trivially.  Moreover, we
   note that secrecy-only and integrity-only labels are implemented
   in "DCLabel.Secrecy" and "DCLabel.Integrity", respectively.
-}

-- | Labels form a partial order according to the &#8849; relation.
-- Specifically, this means that for any two labels @L_1@ and @L_2@ there is a
-- unique label @L_3 = L_1 &#8852; L_2@, known as the /join/, such that
-- @L_1 &#8849; L_3@ and @L_2 &#8849; L_3@. Similarly, there is a unique label
-- @L_3' = L_1 &#8851; L_2@, known as the /meet/, such that
-- @L_3 &#8849; L_1@ and @L_3 &#8849; L_2@. This class defines a /bounded/
-- lattice, which further requires the definition of the /bottom/ &#8869; and
-- /top/ &#8868; elements of the lattice, such that @&#8869; &#8849; L@ and
-- @L &#8849; &#8868;@ for any label @L@.
class Eq a => Lattice a where
  bottom    :: a  -- ^ Bottom of lattice, &#8869;
  top       :: a  -- ^ Top of lattice, &#8868;
  join      :: a -> a -> a  -- ^ Join of two elements, &#8852;
  meet      :: a -> a -> a  -- ^ Meet of two elements, &#8851;
  canflowto :: a -> a -> Bool -- ^ Partial order relation, &#8849;


-- | A components is a conjunction of disjunctions, where @MkComponentAll@ is
-- the constructor that is associated with the logical @False@.
data Component = MkComponentAll
               | MkComponent { component :: Conj }
     deriving (Show, Read)

-- | Components have a unique LNF (see 'ToLNF') form, and equality testing is
-- perfomed on labels of this form.
instance Eq Component where
  (==) MkComponentAll MkComponentAll = True
  (==) MkComponentAll _ = False
  (==) _ MkComponentAll = False
  (==) l1 l2 = (component . toLNF $ l1) == (component . toLNF $ l2)

-- | A component without any disjunctions or conjunctions. This
-- component, conceptually corresponds to the label consisting of
-- a single category containing all principals. Conceptually (in a
-- closed-world system),
-- @emptyComponent = \<{[P_1 &#8897; P_2 &#8897; ...]}\>@.
-- Logically, of course, this is equivalent to @True@.
emptyComponent :: Component
emptyComponent = MkComponent (MkConj [])

-- | The dual of 'emptyComponent', 'allComponent' consists of the conjunction of
-- all possible disjunctions, i.e., it is the label that implies all
-- other labels. Conceptually (in a closed-world system),
-- @allComponent = \<{[P_1] &#8896; [P_2] &#8896; ...}\>@
-- Logically, of course, this is equivalent to @False@.
allComponent :: Component
allComponent = MkComponentAll

-- | Predicate function that returns @True@ if the label corresponds to
-- the 'emptyComponent'.
isEmptyComponent :: Component -> Bool
isEmptyComponent MkComponentAll = False
isEmptyComponent l = and [ null (disj d) | d <- conj (component l) ]

-- | Predicate function that retuns @True@ if the label corresponds to
-- the 'allComponent'.
isAllComponent :: Component -> Bool
isAllComponent MkComponentAll = True
isAllComponent _ = False


--
-- Helper functions
--


-- | Given two components, take the union of the disjunctions, i.e., simply
-- perform an \"and\". Note the new component is not necessarily in LNF.
and_component :: Component -> Component -> Component
and_component l1 l2 | isAllComponent l1 || isAllComponent l2 = allComponent
                    | otherwise = MkComponent {component = MkConj $
                          conj (component l1) ++ conj (component l2)}

-- | Given two components, perform an \"or\".
-- Note that the new component is not necessarily in LNF.
or_component :: Component -> Component -> Component
or_component l1 l2 | isEmptyComponent l1 || isEmptyComponent l2 = emptyComponent
                   | isAllComponent l2 = l1
                   | isAllComponent l1 = l2
                   | otherwise = MkComponent . MkConj $
                                       [ MkDisj (disj d1 ++ disj d2)
                                       | d1 <- (conj (component l1))
                                       , d2 <- (conj (component l2))
                                       , not . null . disj $ d1
                                       , not . null . disj $ d2]

-- | Determines if a conjunction of disjunctions, i.e., a component, implies
-- (in the logical sense) a disjunction. In other words, it checks if
-- d_1 &#8896; ... &#8896; d_n => d_1.
--
-- Properties:
--
--      * &#8704; X, 'allComponent' \``impliesDisj`\` X = True
--
--      * &#8704; X, X \``impliesDisj`\` 'emptyComponent'  = True
--
--      * &#8704; X&#8800;'emptyComponent', 'emptyComponent' \``impliesDisj`\` X = False
--
-- Note that the first two guards are only included
-- for safety; the function is always called with a non-ALL component and
-- non-null disjunction.
impliesDisj :: Component -> Disj -> Bool
impliesDisj l d | isAllComponent l = True   -- Asserts 1
                | null (disj d) = True  -- Asserts 2
                | otherwise = or [ and [ e `elem` (disj d) | e <- disj d1 ]
                                 | d1 <- conj (component l)
                                 , not (isEmptyComponent l) ] -- Asserts 3

-- | Determines if a component logically implies another component.
-- In other words, d_1 &#8896; ... &#8896; d_n => d_1' &#8896; ... &#8896; d_n'.
--
-- Properties:
--
-- 	* &#8704; X, 'allComponent' \``implies`\` X := True
--
--      * &#8704; X&#8800;'allComponent', X \``implies`\` 'allComponent' := False
--
--      * &#8704; X, X \``implies`\` 'emptyComponent' := True
--
--      * &#8704; X&#8800;'emptyComponent', 'emptyComponent' \``implies`\` X := False
implies :: Component -> Component -> Bool
implies l1 l2 | isAllComponent l1 = True -- Asserts 1
              | isAllComponent l2 = False -- Asserts 2
              | otherwise = and [ impliesDisj (toLNF l1) d
                                | d <- conj . component . toLNF $ l2 ]


-- | Removes any duplicate principals from categories, and any duplicate
-- categories from the component. To return a clean component, it sorts the
-- component and removes empty disjunctions.
cleanComponent :: Component -> Component
cleanComponent MkComponentAll = MkComponentAll
cleanComponent l = MkComponent . MkConj . sort . nub $
               [ MkDisj ( (sort . nub) (disj d) ) | d <- conj (component l)
                                                  , not . null $ disj d ]

-- | Class used to reduce labels and components to unique label normal form
-- (LNF), which corresponds to conjunctive normal form of principals. We use
-- this class to overload the reduce function used by the 'Component',
-- 'DCLabel', etc.
class ToLNF a where
  toLNF :: a -> a

-- | Reduce a 'Component' to LNF.
-- First it applies @cleanComponent@ to remove duplicate principals
-- and categories.  Following, it removes extraneous/redundant
-- categories. A category is said to be extraneous if there is another
-- category in the component that implies it.
instance ToLNF Component where
  toLNF MkComponentAll = MkComponentAll
  toLNF l = MkComponent . MkConj $ l' \\ extraneous
    where l' = conj . component $ cleanComponent l
          extraneous = [ d2 | d1 <- l', d2 <- l', d1 /= d2
                            , impliesDisj ((MkComponent . MkConj) [d1]) d2 ]

--
-- DC Labels
--


--
-- DC Labels : (Secrecy, Integrity)
--

-- | A @DCLabel@ is a pair of secrecy and integrity category sets, i.e.,
-- a pair of 'Component's.
data DCLabel = MkDCLabel { secrecy   :: Component -- ^  Integrity category set.
                         , integrity :: Component -- ^ Secrecy category set.
    } deriving (Eq, Show, Read)

-- | Each 'DCLabel' can be reduced a unique label representation in LNF, using
-- the 'toLNF' function.
instance ToLNF DCLabel where
  toLNF l = MkDCLabel { secrecy = toLNF (secrecy l)
                      , integrity = toLNF (integrity l)}

-- | Elements of 'DCLabel' form a bounded lattice, where:
--
-- 	* @&#8869; = \<'emptyComponent', 'allComponent'\>@
--
-- 	* @&#8868; = \<'allComponent', 'emptyComponent'\>@
--
-- 	* @ \<S_1, I_1\> &#8852; \<S_2, I_2\> = \<S_1 &#8896; S_2, I_1 &#8897; I_2\>@
--
-- 	* @ \<S_1, I_1\> &#8851; \<S_2, I_2\> = \<S_1 &#8897; S_2, I_1 &#8896; I_2\>@
--
-- 	* @ \<S_1, I_1\> &#8849; \<S_2, I_2\> = S_2 => S_1 &#8896; I_1 => I_2@
instance Lattice DCLabel where
  bottom = MkDCLabel { secrecy = emptyComponent
                     , integrity = allComponent }
  top = MkDCLabel { secrecy = allComponent
                  , integrity = emptyComponent }
  join l1 l2 = let s3 = (secrecy l1) `and_component` (secrecy l2)
                   i3 = (integrity l1) `or_component` (integrity l2)
               in toLNF $ MkDCLabel { secrecy = s3
                                    , integrity = i3 }
  meet l1 l2 = let s3 = (secrecy l1) `or_component` (secrecy l2)
                   i3 = (integrity l1) `and_component` (integrity l2)
               in toLNF $ MkDCLabel { secrecy = s3
                                    , integrity = i3 }
  canflowto l1 l2 = let l1' = toLNF l1
                        l2' = toLNF l2
                    in ((secrecy l2') `implies` (secrecy l1')) &&
                       ((integrity l1') `implies` (integrity l2'))


--
-- Principals
--

-- | Principal is a simple string representing a source of authority. Any piece
-- of code can create principals, regarless of how untrusted it is. However,
-- for principals to be used in integrity components or be ignoerd a
-- corresponding privilege ('TCBPriv') must be created (by trusted code) or
-- delegated.
newtype Principal = MkPrincipal { name :: B.ByteString }
                  deriving (Eq, Ord, Show, Read)

-- | Generates a principal from an string.
class CreatePrincipal s where
  principal :: s -> Principal

instance CreatePrincipal B.ByteString where
  principal = MkPrincipal

instance CreatePrincipal String where
  principal = MkPrincipal . C.pack

--
-- Privileges
--

{- $privs
As previously mentioned privileges allow a piece of code to bypass certain
information flow restrictions. Like principals, privileges of type 'Priv'
may be created by any piece of code. A privilege is simply a conjunction of
disjunctions, i.e., a 'Component' where a category consisting of a single
principal corresponds to the notion of /owning/ that principal. We, however,
allow for the more general notion of ownership of a category as to create a
privilege-hierarchy. Specifically, a piece of code exercising a privilege @P@
can always exercise privilege @P'@ (instead), if @P' => P@. This is similar to
the DLM notion of \"can act for\", and, as such, we provide a function which
tests if one privilege may be use in pace of another: 'canDelegate'.

Note that the privileges form a partial order over @=>@, such that
@'rootPrivTCB' => P@ and @P => 'noPriv'@ for any privilege @P@.
As such we have a privilege hierarchy which can be concretely built through
delegation, with 'rootPrivTCB' corresponding to the /root/, or all, privileges
from which all others may be created. More specifically, given a minted
privilege @P'@ of type 'TCBPriv', and an un-minted privilege @P@ of type 'Priv',
any piece of code can use 'delegatePriv' to mint @P@, assuming @P' => P@.

Finally, given a set of privileges a piece of code can check if it owns a
category using the 'owns' function.
-}

-- | Privilege object is just a conjunction of disjunctions, i.e., 'Component'.
-- A trusted privileged object must be introduced by trusted code, after which
-- trusted privileged objects can be created by delegation.
data TCBPriv = MkTCBPriv { priv :: Component }
     deriving (Eq, Show)

-- | Untrusted privileged object, which can be converted to a 'TCBPriv' with
-- 'delegatePriv'.
type Priv = Component

-- | Class extending 'Lattice', by allowing for the more relaxed label
-- comparison  @canflowto_p@.
class (Lattice a) => RelaxedLattice a where
        -- | Relaxed partial-order relation
        canflowto_p :: TCBPriv -> a -> a -> Bool


instance RelaxedLattice DCLabel where
  canflowto_p p l1 l2 =
    let l1' =  MkDCLabel { secrecy = (secrecy l1)
                         , integrity = (and_component (priv p) (integrity l1)) }
        l2' =  MkDCLabel { secrecy = (and_component (priv p) (secrecy l2))
                         , integrity = (integrity l2) }
    in canflowto l1' l2'


-- | Given trusted privilege and a \"desired\" untrusted privilege,
-- return a trusted version of the untrusted privilege, if the
-- provided (trusted) privilege implies it.
delegatePriv :: TCBPriv -> Priv -> Maybe TCBPriv
delegatePriv tPriv rPriv = let rPriv' = toLNF rPriv
                           in case (priv tPriv) `implies` rPriv' of
                                True -> Just (MkTCBPriv rPriv')
                                False -> Nothing

-- | Privilege object corresponding to no privileges.
noPriv :: TCBPriv
noPriv = MkTCBPriv { priv = emptyComponent }

-- | Privilege object corresponding to the \"root\", or all privileges.
-- Any other privilege may be delegated using this privilege object and it must
-- therefore not be exported to untrusted code.
rootPrivTCB :: TCBPriv
rootPrivTCB = MkTCBPriv { priv = allComponent }

-- | This function creates any privilege object given an untrusted
-- privilege 'Priv'. Note that this function should not be exported
-- to untrusted code.
createPrivTCB :: Priv -> TCBPriv
createPrivTCB = fromJust . (delegatePriv rootPrivTCB)

instance Semigroup TCBPriv where
    p1 <> p2 = createPrivTCB $ toLNF ((priv p1) `and_component` (priv p2))

-- | @TCBPriv@ is an instance of 'Monoid'.
instance Monoid TCBPriv where
  mempty = noPriv


-- | Class used for checking if a computation can use a privilege in place of
-- the other. This notion is similar to the DLM \"can-act-for\".
class CanDelegate a b where
        -- | Can use first privilege in place of second.
        canDelegate :: a -> b -> Bool

instance CanDelegate Priv Priv where
  canDelegate p1 p2 = p1 `implies` p2

instance CanDelegate Priv TCBPriv where
  canDelegate p1 p2 = p1 `implies` (priv p2)

instance CanDelegate TCBPriv Priv where
  canDelegate p1 p2 = (priv p1) `implies` p2

instance CanDelegate TCBPriv TCBPriv where
  canDelegate p1 p2 = (priv p1) `implies` (priv p2)


-- | We say a 'TCBPriv' privilege object owns a category when the privileges
-- allow code to bypass restrictions implied by the category. This is the
-- case if and only if the 'TCBPriv' object contains one of the 'Principal's
-- in the 'Disj'. This class is used to check ownership
class Owns a where
    -- | Checks if category restriction can be bypassed given the privilege.
    owns :: TCBPriv -> a -> Bool

instance Owns Disj where
  owns p d = priv p `impliesDisj` d

instance Owns Component where
  owns p l = priv p `implies` l



-- | Class used to convert list of principals to a disjunction category and
-- vice versa.
class DisjToFromList a where
    listToDisj :: [a] -> Disj -- ^ Given list return category.
    disjToList :: Disj -> [a] -- ^ Given category return list.

-- | To/from 'Principal's and 'Disj'unction categories.
instance DisjToFromList Principal where
  listToDisj ps = MkDisj ps
  disjToList d = disj d

-- | To/from 'String's and 'Disj'unction categories.
instance DisjToFromList String where
  listToDisj ps = MkDisj $ map (principal . C.pack) ps
  disjToList d = map (C.unpack . name) $ disj d

-- | To/from 'ByteString's and 'Disj'unction categories.
instance DisjToFromList B.ByteString where
  listToDisj ps = MkDisj $ map principal ps
  disjToList d = map name $ disj d

-- | Given a list of categories, return a component.
listToComponent :: [Disj] -> Component -- ^ Given list return category.
listToComponent = MkComponent . MkConj

-- | Given a component return a list of categories.
componentToList :: Component -> [Disj] -- ^ Given category return list.
componentToList = conj . component



--
-- Serialize instances
--


instance Serialize Principal where
  put = put . name
  get = MkPrincipal <$> get

instance Serialize Disj where
  put = put . disj
  get = MkDisj <$> get

instance Serialize Conj where
  put = put . conj
  get = MkConj <$> get

instance Serialize Component where
  put c | c == MkComponentAll = put (Nothing :: Maybe Conj)
        | otherwise           = put (Just $ component c)
  get = do mc <- get
           case mc of
             Nothing -> return MkComponentAll
             Just c -> return $ MkComponent c

instance Serialize DCLabel where
  put (MkDCLabel s i) = put s >> put i
  get = do s <- get
           i <- get
           return $ MkDCLabel s i

