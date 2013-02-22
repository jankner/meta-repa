{-# LANGUAGE GADTs #-}
module Core where

import FOAS (reducel3,reducel4,isAtomic)
import qualified FOAS as FO
import qualified HOAS as HO



toFOAS :: HO.Expr a -> FO.Expr
toFOAS (HO.Var v) = FO.Var v

toFOAS (HO.Binop op a b) =
  case op of
    HO.Plus  -> FO.BinOp FO.Plus  (toFOAS a) (toFOAS b)
    HO.Minus -> FO.BinOp FO.Minus (toFOAS a) (toFOAS b)
    HO.Mult  -> FO.BinOp FO.Mult  (toFOAS a) (toFOAS b)
toFOAS (HO.Abs a) = FO.Abs (toFOAS a)
toFOAS (HO.Signum a) = FO.Signum (toFOAS a)
toFOAS (HO.FromInteger n) = FO.FromInteger n

toFOAS (HO.Quot a b) = FO.BinOp FO.Quot (toFOAS a) (toFOAS b)
toFOAS (HO.Rem  a b) = FO.BinOp FO.Rem  (toFOAS a) (toFOAS b)
toFOAS (HO.And  a b) = FO.BinOp FO.And  (toFOAS a) (toFOAS b)
toFOAS (HO.Or   a b) = FO.BinOp FO.Or   (toFOAS a) (toFOAS b)
toFOAS (HO.Min  a b) = FO.BinOp FO.Min  (toFOAS a) (toFOAS b)
toFOAS (HO.Max  a b) = FO.BinOp FO.Max  (toFOAS a) (toFOAS b)

toFOAS (HO.Equal    a b) = FO.Compare FO.EQU (toFOAS a) (toFOAS b)
toFOAS (HO.NotEqual a b) = FO.Compare FO.NEQ (toFOAS a) (toFOAS b)
toFOAS (HO.GTH      a b) = FO.Compare FO.GTH (toFOAS a) (toFOAS b)
toFOAS (HO.LTH      a b) = FO.Compare FO.LTH (toFOAS a) (toFOAS b)
toFOAS (HO.GTE      a b) = FO.Compare FO.GEQ (toFOAS a) (toFOAS b)
toFOAS (HO.LTE      a b) = FO.Compare FO.LEQ (toFOAS a) (toFOAS b)

toFOAS (HO.Tup2 a b) = FO.Tup2 (toFOAS a) (toFOAS b)
toFOAS (HO.Fst a) = FO.Fst (toFOAS a)
toFOAS (HO.Snd a) = FO.Snd (toFOAS a)

toFOAS (HO.Let a f) = FO.Let v (toFOAS a) e
  where e = toFOAS $ f (HO.Var v)
        v = getVar e

toFOAS (HO.Return a) = FO.Return (toFOAS a)
toFOAS (HO.Bind a f) = FO.Bind (toFOAS a) (toFOASFun f)

toFOAS (HO.IterateWhile cond step init) =
  FO.IterateWhile
    (toFOASFun cond)
    (toFOASFun step)
    (toFOAS init)
toFOAS (HO.WhileM cond step action init) =
  FO.WhileM
    (toFOASFun cond)
    (toFOASFun step)
    (toFOASFun action)
    (toFOAS init)

toFOAS (HO.RunMutableArray a) = FO.RunMutableArray (toFOAS a)
toFOAS (HO.ReadIArray a b) = FO.ReadIArray (toFOAS a) (toFOAS b)
toFOAS (HO.ArrayLength a) = FO.ArrayLength (toFOAS a)

toFOAS (HO.NewArray a) = FO.NewArray (toFOAS a)
toFOAS (HO.ReadArray a b) = FO.ReadArray  (toFOAS a) (toFOAS b)
toFOAS (HO.WriteArray a b c) = FO.WriteArray (toFOAS a) (toFOAS b) (toFOAS c)

toFOAS (HO.ParM n f) = FO.ParM (toFOAS n) (toFOASFun f)
toFOAS (HO.Skip) = FO.Skip
toFOAS (HO.Print a) = FO.Print (toFOAS a)

toFOASFun :: (HO.Expr a -> HO.Expr b) -> FO.Expr
toFOASFun f = FO.Lambda v e
  where e = toFOAS $ f (HO.Var v)
        v = getVar e


getVar :: FO.Expr -> Int
getVar = FO.exprFold getVar' max max3 max4

getVar' :: (FO.Expr -> Int) -> FO.Expr -> Int
getVar' f (FO.Lambda i _) = i+1
getVar' f (FO.Let i _ _) = i+1
getVar' f e | isAtomic e = 0
            | otherwise  = f e

max3 :: Ord a => a -> a -> a -> a
max3 = reducel3 max

max4 :: Ord a => a -> a -> a -> a -> a
max4 = reducel4 max

