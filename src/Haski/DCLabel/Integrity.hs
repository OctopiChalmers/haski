

{-# LANGUAGE CPP #-}
#if defined(__GLASGOW_HASKELL__) && (__GLASGOW_HASKELL__ >= 702)
{-# LANGUAGE Trustworthy #-}
#endif
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
-- | This module implements integrity-only DC Labels.
module Haski.DCLabel.Integrity ( ILabel(..) ) where

import Haski.DCLabel.Core

-- | An integrity-only DC label.
newtype ILabel = MkILabel DCLabel
    deriving (Eq, Show, Read)

instance ToLNF ILabel where
    toLNF (MkILabel l) = MkILabel (toLNF l)

instance Lattice ILabel where
  bottom = MkILabel bottom
  top = MkILabel top
  join (MkILabel l1) (MkILabel l2) = MkILabel $
    join l1 { secrecy = emptyComponent } l2 { secrecy = emptyComponent }
  meet (MkILabel l1) (MkILabel l2) = MkILabel $
    meet l1 { secrecy = emptyComponent } l2 { secrecy = emptyComponent }
  canflowto (MkILabel l1) (MkILabel l2) =
    canflowto l1 { secrecy = emptyComponent } l2 { secrecy = emptyComponent }

instance RelaxedLattice ILabel where
  canflowto_p p (MkILabel l1) (MkILabel l2) =
    canflowto_p p l1 { secrecy = emptyComponent } l2 { secrecy = emptyComponent }

