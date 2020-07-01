module Haski.Backend where

import Haski.OBC

import Text.PrettyPrint.HughesPJClass (Pretty)

class Pretty a => Backend a where
    compileClasses  :: [Class p] -> a

