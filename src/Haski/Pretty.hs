{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Haski.Pretty where

import Prelude hiding ((<>))
import Data.List
import Data.Maybe (fromMaybe)
import Data.Coerce (coerce, Coercible)
import Text.PrettyPrint
import Text.PrettyPrint.HughesPJClass hiding (pPrintList)

import Haski.Core
import Haski.Util
import Haski.Pass (ForallArg)
import Haski.Clock
import Haski.Norm
import Haski.OBC hiding (Exp,Let)
import qualified Haski.OBC as OBC
import Haski.Enum

instance (Show a) => Show (Stream a) where
    show = show . pPrint

instance Show Def where
    show = show . pPrint

instance {-# OVERLAPPING #-} Show [Def] where
    show = show . pPrint

instance Pretty Clock where
    pPrint Base        = text "Base"
    pPrint (On ck c x) = pPrint ck
        <+> text "`On`"
        <+> text (getName x)
        <> lparen
        <> pPrint c
        <> rparen

instance Pretty CkTy where
    pPrint BaseTy      = text "BaseTy"
    pPrint (OnTy cl c v) = text "On"
        <+> lparen
        <> pPrint cl
        <> rparen
        <+> pPrint c
        <+> lbrace
        <> text (getName v)
        <+> rbrace
    pPrint (TyVar x)     = text "Var" <+> pPrint x

pPrintAnn :: (Pretty a) => Bool -> a -> Doc
pPrintAnn s p | s
    = char '@' <> pPrint p
pPrintAnn s p | otherwise
    = empty

pPrintExp :: (ForallArg p Pretty)
    => Bool -> GExp p a -> Doc
pPrintExp s = goExp
    where
    goExp (GVal p x) = pPrint x <+> pPrintAnn s p
    goExp (GVar p x) = text (getName x)
    goExp (GFby p x e) = pPrint x
        <+> text "`Fby`"
        <+> goExp e
        <+> pPrintAnn s p
    goExp (GWhn p e (x,c)) = goExp e <+> text "`When`"
        <+> lparen
            <> text (getName x)
            <+> text "=="
            <+> pPrint c
            <> rparen
        <+> pPrintAnn s p
    goExp (GMrg p x m) = text "Merge"
        <+> text (getName x) <+> pPrintAnn s p
        $$ nest 2 (foldr (\e' acc -> acc $$ goExp e' ) empty m)
    goExp (GAdd p e1 e2) = lparen
        <> goExp e1
        <+> char '+'
        <+> goExp e2
        <+> pPrintAnn s p
        <> rparen
    goExp (GMul p e1 e2) = lparen
        <> goExp e1
        <+> char '*'
        <+> goExp e2
        <+> pPrintAnn s p
        <> rparen
    goExp (GAbs p e) = lparen
        <> text "Abs"
        <+> goExp e
        <> rparen
    goExp (GSig p e) = lparen
        <> text "Sig"
        <+> goExp e
        <> rparen
    goExp (GNeg p e) = lparen
        <> text "Neg"
        <+> goExp e
        <> rparen

instance {-# OVERLAPPING #-} Pretty (Stream a) where
    pPrint = pPrintExp False

instance (ForallArg p Pretty)
    => Pretty (GExp p a) where
    pPrint = pPrintExp True

instance (ForallArg p Pretty) => Pretty (GDef p) where
    pPrint (Let x e) =
        text "Let"
        <+> text (getName x)
        <+> char '='
        <+> pPrint e
    pPrint (App x nodeName args) =
        text "App"
        <+> text (getName x)
        <+> char '='
        <+> text nodeName
        <+> pPrintVia @(PList (Ex (GExp p))) args

instance {-# OVERLAPPING #-} Pretty (Def) where
    pPrint (Let x e) =
        text "Let"
        <+> text (getName x)
        <+> char '='
        <+> pPrint e
    pPrint (App x nodeName args) =
        text "App"
        <+> text (getName x)
        <+> char '='
        <+> text nodeName
        <+> pPrintVia @(PList (Ex Stream)) args

instance Pretty (Var a) where
    pPrint = text . getName

instance (forall a . Pretty a => Pretty (f a)) => Pretty (Ex f) where
    pPrint (Ex x) = pPrint x

instance (ForallArg p Pretty) => Pretty (GNode p) where
    pPrint (GNode name vars defs res) =
        text "node" <+> text name
        <+> pPrintVia @(PList (Ex Var)) vars
        $$ nest 2 (pPrintVia @(PList (GDef p)) $ defs)
        $$ text "return" <+> pPrint res

instance {-# OVERLAPPING #-} Pretty (Node) where
    pPrint (GNode name vars defs res) =
        text "node" <+> text name
        <+> pPrintVia @(PList (Ex Var)) vars
        $$ nest 2 (pPrintVia @(PList Def) defs)
        $$ text "return" <+> pPrint res

pPrintVia :: forall b a . (Pretty b, Coercible a b) => a -> Doc
pPrintVia = pPrint @b . coerce

instance {-# OVERLAPPING #-} (ForallArg p Pretty)
    => Pretty (NGExp p a) where
    pPrint = pPrint . fst . unpack

instance (ForallArg p Pretty) => Pretty (NCA p a) where
    pPrint (NExp e) = pPrint e
    pPrint (NMrg p x m) =  text "Merge"
        <+> text (getName x) <+> pPrintAnn True p
        $$ nest 2 (foldr (\e' acc -> acc $$ pPrint e' ) empty m)

instance (ForallArg p Pretty) => Pretty (EQ p) where
    pPrint (LetEq x e) =
        text (getName x)
        <+> char '='
        <+> pPrint e
    pPrint (FbyEq p x v e) =
        text (getName x)
        <+> char '='
        <+> pPrint v
        <+> text "`Fby`"
        <+> pPrint e
        <+> pPrintAnn False p
    pPrint (AppEq x nodeName args) =
        text (getName x)
        <+> char '='
        <+> text nodeName
        <+> pPrintVia @(PList (Ex (GExp p))) (map (exMap (fst . unpack)) args)

instance ForallArg p Pretty => Pretty (EQNode p) where
    pPrint (EQNode name vars defs res) =
        text "node" <+> text name
        <+> pPrintVia @(PList (Ex Var)) vars
        $$ nest 2 (pPrintVia @(PList (EQ p)) defs)
        $$ text "return" <+> pPrint res

instance Pretty a => Pretty (Field a) where
    pPrint (Field (x,v)) = pPrint x
        <+> text ":="
        <+> pPrint v

instance Pretty Obj where
    pPrint (Obj name typ) = text name
        <+> text ":"
        <+> text typ

instance ForallArg p Pretty => Pretty (OBC.Exp p a) where
    pPrint (OBC.Var x)      = pPrint x
    pPrint (OBC.Ref x)      = text "state"
        <> lparen
        <> pPrint x
        <> rparen
    pPrint (OBC.Val x)      = pPrint x
    pPrint (OBC.Add e1 e2)  = lparen
        <> pPrint e1
        <+> char '+'
        <+> pPrint e2
        <> rparen
    pPrint (OBC.Mul e1 e2)  = lparen
        <> pPrint e1
        <+> char '*'
        <+> pPrint e2
        <> rparen
    pPrint (OBC.Abs e)  = text "abs"
        <> lparen
        <> pPrint e
        <> rparen
    pPrint (OBC.Sig e)  = text "sig"
        <> lparen
        <> pPrint e
        <> rparen
    pPrint (OBC.Neg e)  = text "sig"
        <> lparen
        <> pPrint e
        <> rparen

instance ForallArg p Pretty => Pretty (Stmt p) where
    pPrint (OBC.Let x e) = pPrint x <+> char '=' <+> pPrint e
    pPrint (OBC.Ass x e) = pPrint x <+> text ":=" <+> pPrint e
    pPrint (Skip)        = text "skip"
    pPrint (Seq s1 s2)   = pPrint s1 <> text ";" $$ pPrint s2
    pPrint (Case sc bs)  =  text "case"
        <+> pPrint sc
        <+> text "of"
        <+> lbrace
        $$ nest 2 (foldr
            (\s acc -> acc $$ (text "_ ->" <+> pPrint s))
            empty bs)
        $$ rbrace
    pPrint (CallReset obj)  = text (getName obj)
        <> char '.'
        <> text "reset"
        <> lparen <> rparen
    pPrint (CallStep x obj args) = pPrint x
        <+> char '='
        <+> text (getName obj)
        <> char '.'
        <> text "step"
        <> (pPrintVia @(PList (Ex (OBC.Exp p))) args)

pPrintMethod :: forall p a . ForallArg p Pretty
    => Name -> [Ex Var] -> [Stmt p] -> Maybe (OBC.Exp p a) -> Doc
pPrintMethod name args body res = text name
    <> (pPrintVia @(PList (Ex Var)) args)
    <+> lbrace
    $$ nest 2 (
        (pPrintVia @(PList (Stmt p)) body)
        $$ fromMaybe
            empty
            ((<+>) (text "return")
                . flip (<>) (char ';')
                . pPrint <$> res))
    $$ rbrace

instance ForallArg p Pretty => Pretty (Step p) where
    pPrint (Step args res body) =
        pPrintMethod "step" args body (Just res)

instance ForallArg p Pretty => Pretty (Class p) where
    pPrint (Class name fields objs reset step) =
        text "class" <+> text name <+> lbrace
        $$ nest 2 (
            (pPrintVia @(PList (Ex Field)) fields)
            $$ (pPrintVia @(PList Obj) objs)
            $$ pPrintMethod "reset" [] reset Nothing
            $$ pPrint step
        )
        $$ rbrace

newtype PList a = PList [ a ]
    deriving Foldable

pPrintPListH :: Pretty a => (Doc,Doc) -> Doc -> PList a -> Doc
pPrintPListH (beg,end) sep (PList xs) = beg
    <> (foldr (<>) empty $ intersperse sep (map pPrint xs))
    <> end

pPrintPListV :: Pretty a => Doc -> PList a -> Doc
pPrintPListV term = foldr (\d acc -> (pPrint d <> term) $$ acc) empty

instance (forall a . Pretty a => Pretty (f a))
    => Pretty (PList (Ex f)) where
    pPrint = pPrintPListH (lparen,rparen) comma

instance {-# OVERLAPPING #-} Pretty (PList (Ex Field)) where
    pPrint = pPrintPListH (text "field ",char ';') (text ", ")

instance {-# OVERLAPPING #-} Pretty (PList Obj) where
    pPrint = pPrintPListH (text "instance ",char ';') (text ", ")

instance {-# OVERLAPPING #-} Pretty (PList Def) where
    pPrint = pPrintPListV empty

instance ForallArg p Pretty => Pretty (PList (GDef p)) where
    pPrint = pPrintPListV empty

instance ForallArg p Pretty => Pretty (PList (Stmt p)) where
    pPrint = pPrintPListV (char ';')

instance ForallArg p Pretty => Pretty (PList (EQ p)) where
    pPrint = pPrintPListV empty
