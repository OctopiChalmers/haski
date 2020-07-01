{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
{-# LANGUAGE Trustworthy #-}
#endif
{-| This module exports a function 'prettyShow' that pretty prints 'Principal's,
'Disj'unctions, 'Conj'unctions, 'Component's and 'DCLabel's.
-}
module Haski.DCLabel.PrettyShow (PrettyShow(..), prettyShow) where

import Prelude hiding ((<>))
import Haski.DCLabel.Core
import Haski.DCLabel.Secrecy
import Haski.DCLabel.Integrity
import Text.PrettyPrint

-- | Class used to create a 'Doc' type of DCLabel-related types
class PrettyShow a where
    pShow :: a -> Doc -- ^ Convert to 'Doc'.

-- | Render a 'PrettyShow' type to a string.
prettyShow :: PrettyShow a => a -> String
prettyShow = render . pShow

instance PrettyShow Disj where
    pShow (MkDisj xs) = bracks $ showDisj xs
                where
                showDisj []     = empty
                showDisj [x]    = pShow x
                showDisj (x:ys) = pShow x <+> ( text "\\/") <+> showDisj ys
                bracks x = lbrack <> x <> rbrack

instance PrettyShow Conj where
    pShow (MkConj [])     = text "True"
    pShow (MkConj (x:[])) = pShow x
    pShow (MkConj (x:xs)) = pShow x <+> (text "/\\") <+> pShow (MkConj xs)

instance PrettyShow Component where
    pShow MkComponentAll     = text "False"
    pShow l = let (MkComponent c) = toLNF l ; showC = pShow c
                in if c == MkConj [] then showC else braces showC

instance PrettyShow DCLabel where
    pShow (MkDCLabel s  i) = angle $ pShow s <+> comma <+> pShow i
        where angle txt = (text "<") <> txt <> (text ">")

instance PrettyShow Principal where
    pShow (MkPrincipal s) = text (show s)

instance PrettyShow TCBPriv where
    pShow (MkTCBPriv p) = pShow p

instance PrettyShow SLabel where
    pShow (MkSLabel dcL) = pShow . secrecy $ dcL

instance PrettyShow ILabel where
    pShow (MkILabel dcL) = pShow . integrity $ dcL
