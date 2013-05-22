{-# OPTIONS_GHC -fth #-}
module GenInstance where

import Language.Haskell.TH
import Language.Haskell.TH.Lib

import MaybeNF


deriveMaybeNFTups :: Int -> Q [Dec]
deriveMaybeNFTups n = mapM deriveMaybeNFTup [2..n]

deriveMaybeNFTup :: Int -> Q Dec
deriveMaybeNFTup n = return $ InstanceD cxt instT [funDec]
  where vars = map mkName (take n names)
        varsT = map VarT vars
        varsE = map VarE vars
        cxt = map (\t -> ClassP ''MaybeNF [t]) varsT
        instT = AppT (ConT $ ''MaybeNF) tuple 
        tuple = foldl AppT (TupleT n) varsT
        funDec = FunD (mkName "maybeDeepSeq") [Clause [tupPat, VarP (mkName "x0")] body []]
        tupPat = TupP (map VarP vars)
        body = NormalB (foldr AppE (VarE (mkName "x0")) es)
        es = map (AppE mbdsq) varsE
        mbdsq = VarE (mkName "maybeDeepSeq")

names :: [String]
names = let initial = map (:[]) ['a'..'z']
        in initial ++ concatMap (\n -> map (n ++) initial) names
