{-# LANGUAGE LambdaCase      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns    #-}

{- | Functions for generating boilerplate-code. -}

module Haski.TH where

import Control.Monad (zipWithM)
import Language.Haskell.TH

import qualified Data.List as List

import qualified Haski.Core
import qualified Haski.Lang
import qualified Haski.Util


{- | Create smart constructors for some partition type.
-}
mkConstructors :: Name -> Q [Dec]
mkConstructors victim = do
    TyConI d <- reify victim
    genConstructors d
  where
    genConstructors :: Dec -> Q [Dec]
    genConstructors (DataD [] tName [] _ constructors _) = do
        funs <- mapM genCon constructors
        sigs <- mapM (genSig (ConT tName)) constructors
        pure $ funs ++ sigs
    genConstructors _ = err $ concat
        [ "Invalid data declaration for type `", show victim, "`. Currently"
        , " only allows very simple data declarations, e.g. no support for"
        , " type variables."
        ]

    genSig :: Type -> Con -> Q Dec
    genSig retType (NormalC cName (map snd -> types)) = do
        let fName = mkName ('_' : nameBase cName)
        let retTypeM = AppT (ConT ''Haski.Lang.Haski) retType
        let typeSig = List.foldr1 (AppT . AppT ArrowT) $ types ++ [retTypeM]
        pure $ SigD fName typeSig
    genSig _ _ = invalidCon

    genCon :: Con -> Q Dec
    genCon (NormalC cName (map snd -> types)) = do
        let fName = mkName ('_' : nameBase cName)
        fClause <- genClause cName types
        pure $ FunD fName [fClause]
    genCon _ = invalidCon

    genClause :: Name -> [Type] -> Q Clause
    genClause cName types = do
        let numArgs = length types
        let argNames = take numArgs (infVarNames "v")
        let pats = map VarP argNames
        body <- genBody argNames
        pure $ Clause pats body []
      where
        genBody :: [Name] -> Q Body
        genBody argNames = do
            e <- [e| Haski.Core.newFieldTagger |]
            justStrings <- zipWithM
                (\ t n ->
                    [e| $(stringE . (++ "_" ++ show n) . typeToString $ t)
                    |])
                types
                [0 :: Int ..]  -- Need this for constructors with multiple
                               -- fields of the same type.
            -- justStrings:
            -- [Just "Temp0", Just "Humidity1", ...]
            let bindApps = map (flip BindS . AppE e) justStrings

            let tagNames = take (length argNames) (infVarNames "tag")
            let bindings = zipWith (\ bind tag -> bind (VarP tag)) bindApps tagNames
            -- bindings:
            -- v0 <- newFieldTag
            -- v1 <- newFieldTag
            -- ...

            let conArgs = zipWith (\ t a -> AppE (VarE t) (VarE a)) tagNames argNames
            let construction = List.foldl' AppE (ConE cName) conArgs
            returnStmt <- NoBindS <$> [e| return $(pure construction) |]
            -- returnStmt:
            -- pure $ SomeConstructor (t0 v0) (t0 v1) ...

            pure . NormalB . DoE $ bindings ++ [returnStmt]

    infVarNames :: String -> [Name]
    infVarNames prefix = map (mkName . (prefix ++) . show) ([0 ..] :: [Int])

    invalidCon :: a
    invalidCon = err $ concat
        [ "Invalid constructor form in declaration of data type ` "
        , show victim, "`. Only 'normal' constructors are allowed;"
        , " no record syntax, no existential quantification etc."
        ]

    err :: String -> a
    err s = error $ "Error in TH function `mkConstructors`: " ++ s

typeToString :: Type -> String
typeToString = \case
    ConT name -> nameBase name
    AppT t1 t2 -> typeToString t1 ++ "_" ++ typeToString t2
    -- ForallT [TyVarBndr] Cxt Type
    -- SigT Type Kind
    -- VarT Name
    -- PromotedT Name
    -- TupleT Int
    -- UnboxedTupleT Int
    -- ArrowT
    -- EqualityT
    -- ListT
    -- PromotedTupleT Int
    -- PromotedNilT
    -- PromotedConsT
    -- StarT
    -- ConstraintT
    -- Constraint
    -- LitT TyLit
    t -> err t
  where
    err :: Type -> a
    err t' = error $ concat
        [ "Error in TH function `typeToString`, unexpected variant of type! "
        , "If your type is fancy, it might not work so well! "
        , "\nType: ", show t'
        ]
