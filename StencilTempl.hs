{-# LANGUAGE TemplateHaskell, QuasiQuotes, ParallelListComp #-}
module StencilTempl (stencilM) where

import Stencil
import HOAS

import StencilExp

import Language.Haskell.TH
import Language.Haskell.TH.Quote


test = [stencilE| a+b,           b*3-c, c/2 ;
                  1-c,           2+e,   3/d ;
                  x > 3 ? 1 : 2, y,     z |]

translateExpr :: SExpr -> Exp
translateExpr (ECond e1 e2 e3) =
  VarE (mkName "If")
    `AppE` translateExpr e1
    `AppE` translateExpr e2
    `AppE` translateExpr e3
translateExpr (EOr e1 e2) =
  AppE (VarE (mkName "Binop")) (VarE (mkName "Or"))
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EAnd e1 e2) =
  AppE (VarE (mkName "Binop")) (VarE (mkName "And"))
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (ELt e1 e2) = 
  VarE (mkName "LTH")
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EGt e1 e2) = 
  VarE (mkName "GTH")
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (ELtE e1 e2) = 
  VarE (mkName "LTE")
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EGtE e1 e2) = 
  VarE (mkName "GTE")
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EEq e1 e2) = 
  VarE (mkName "Equal")
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (ENEq e1 e2) = 
  VarE (mkName "NotEqual")
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EPlus e1 e2) =
  AppE (VarE (mkName "Binop")) (VarE (mkName "Plus"))
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EMinus e1 e2) =
  AppE (VarE (mkName "Binop")) (VarE (mkName "Minus"))
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EMult e1 e2) =
  AppE (VarE (mkName "Binop")) (VarE (mkName "Mult"))
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (EDiv e1 e2) =
  AppE (VarE (mkName "Binop")) (VarE (mkName "FDiv"))
    `AppE` translateExpr e1
    `AppE` translateExpr e2
translateExpr (ENeg e) =
  VarE (mkName "negate")
    `AppE` translateExpr e
translateExpr (EVar (Ident n)) = VarE (mkName n)
translateExpr (EInt i) = LitE (IntegerL i)
translateExpr (EDouble d) = LitE (RationalL $ toRational d)


stencilM :: QuasiQuoter
stencilM = QuasiQuoter
                { quoteExp      = parseStencil2
                , quotePat      = undefined
                , quoteType     = undefined
                , quoteDec      = undefined }


-- | Parse a stencil definition.
--   TODO: make this more robust.
parseStencil2 :: String -> Q Exp
parseStencil2 str
 = let
        -- Determine the extent of the stencil based on the layout.
        -- TODO: make this more robust. In particular, handle blank
        --       lines at the start of the definition.
        line1 : _       = lines str
        sizeX           = fromIntegral $ length $ lines str
        sizeY           = fromIntegral $ length $ words line1

        -- TODO: this probably doesn't work for stencils who's extents are even.
        minX            = negate (sizeX `div` 2)
        minY            = negate (sizeY `div` 2)
        maxX            = sizeX `div` 2
        maxY            = sizeY `div` 2

        -- List of coefficients for the stencil.
        coeffs          = (map read $ words str) :: [Integer]

   in   makeStencil2' sizeX sizeY
         $ filter (\(_, _, v) -> v /= 0)
         $ [ (fromIntegral y, fromIntegral x, fromIntegral v)
                | y     <- [minX, minX + 1 .. maxX]
                , x     <- [minY, minY + 1 .. maxY]
                | v     <- coeffs ]



makeStencil2'
        :: Integer -> Integer
        -> [(Integer, Integer, Integer)]
        -> Q Exp

makeStencil2' sizeX sizeY coeffs =
  do things <- makeThings coeffs
     getFuns <- makeGetFuns [0..length coeffs-1]
     return
      $ VarE (mkName "makeStencil2") 
                        `AppE` (LitE (IntegerL sizeX)) 
                        `AppE` (LitE (IntegerL sizeY))
                        `AppE` things
                        `AppE` getFuns
      


makeGetFuns :: [Int] -> Q Exp
makeGetFuns [n]    = [| Ein $(makeGetFun n) |]
makeGetFuns (n:ns) = [| $(makeGetFun n) ::. $(makeGetFuns ns) |]

makeGetFun :: Int -> Q Exp
makeGetFun n = 
  do ve <- newName "e"
     [| GetFun $(lam1E (varP ve) [| getN $(integerToNat n) $(varE ve) |]) |]

integerToNat :: Int -> Q Exp
integerToNat 0 = [| Z |]
integerToNat n = [| S $(integerToNat (n-1)) |]

makeThings :: [(Integer, Integer, Integer)] -> Q Exp
makeThings [(x,y,v)]        = [| Ein $(makeThing (x,y,v)) |]
makeThings ((x,y,v):coeffs) = [| $(makeThing (x,y,v)) ::. $(makeThings coeffs) |]

makeThing :: (Integer, Integer, Integer) -> Q Exp
makeThing (x,y,v) = [| Thing (fromInteger x, fromInteger y) (fromInteger v) |] --((varE 'Thing) `appE` (tupE [ litE $ IntegerL x, litE $ IntegerL y]) `appE` [| fromInteger v |])
