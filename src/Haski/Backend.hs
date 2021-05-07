module Haski.Backend where

import Haski.OBC

import Text.PrettyPrint.HughesPJClass (Pretty)

-- Unused for now, after changing how compilation works in Haski.Backend.C
class Pretty a => Backend a where
    compileClasses  :: [Class p] -> a

