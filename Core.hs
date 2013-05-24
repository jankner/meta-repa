{-# LANGUAGE GADTs #-}
module Core where

import FOAS (reducel3,reducel4,isAtomic)
import qualified FOAS as FO
import qualified FOASTyped as FOT
import qualified HOAS as HO
import qualified FOASCommon as FO
import Types


translateType :: HO.Type a -> Type
translateType (HO.TConst tc) = TConst (translateTConst tc)
translateType (HO.TFun  t1 t2) = TFun  (translateType t1) (translateType t2)
translateType (HO.TTup2 t1 t2) = TTup2 (translateType t1) (translateType t2)
translateType (HO.TTupN ts) = TTupN (HO.tupMap translateType ts)
translateType (HO.TMArr t) = TMArr (translateType t)
translateType (HO.TIArr t) = TIArr (translateType t)
translateType (HO.TIO   t) = TIO   (translateType t)

translateTConst :: HO.TypeConst a -> TypeConst
translateTConst HO.TInt = TInt
translateTConst HO.TInt64 = TInt64
translateTConst HO.TWord = TWord
translateTConst HO.TWord64 = TWord64
translateTConst HO.TFloat = TFloat 
translateTConst HO.TDouble = TDouble 
translateTConst HO.TBool = TBool 
translateTConst HO.TUnit = TUnit

toFOAS :: HO.Expr a -> FO.Expr
toFOAS = FO.fixTuples . toFOAS'

toFOAS' :: HO.Expr a -> FO.Expr
toFOAS' (HO.Var v) = FO.Var v

toFOAS' (HO.Binop op a b) =
  case op of
    HO.Plus  -> FO.BinOp FO.Plus  (toFOAS' a) (toFOAS' b)
    HO.Minus -> FO.BinOp FO.Minus (toFOAS' a) (toFOAS' b)
    HO.Mult  -> FO.BinOp FO.Mult  (toFOAS' a) (toFOAS' b)
    HO.Quot  -> FO.BinOp FO.Quot  (toFOAS' a) (toFOAS' b)
    HO.Rem   -> FO.BinOp FO.Rem   (toFOAS' a) (toFOAS' b)
    HO.Div   -> FO.BinOp FO.Div   (toFOAS' a) (toFOAS' b)
    HO.Mod   -> FO.BinOp FO.Mod   (toFOAS' a) (toFOAS' b)
    HO.FDiv  -> FO.BinOp FO.FDiv  (toFOAS' a) (toFOAS' b)
    HO.And   -> FO.BinOp FO.And   (toFOAS' a) (toFOAS' b)
    HO.Or    -> FO.BinOp FO.Or    (toFOAS' a) (toFOAS' b)
    HO.Min   -> FO.BinOp FO.Min   (toFOAS' a) (toFOAS' b)
    HO.Max   -> FO.BinOp FO.Max   (toFOAS' a) (toFOAS' b)
    HO.Xor   -> FO.BinOp FO.Xor   (toFOAS' a) (toFOAS' b)
    HO.BAnd  -> FO.BinOp FO.BAnd  (toFOAS' a) (toFOAS' b)
    HO.BOr   -> FO.BinOp FO.BOr   (toFOAS' a) (toFOAS' b)
toFOAS' (HO.Abs a)    = FO.UnOp FO.Abs    (toFOAS' a)
toFOAS' (HO.Signum a) = FO.UnOp FO.Signum (toFOAS' a)
toFOAS' (HO.Recip a)  = FO.UnOp FO.Recip  (toFOAS' a)
toFOAS' (HO.FromInteger  t i) = FO.FromInteger (translateTConst t) i
toFOAS' (HO.FromRational t r) = FO.FromRational (translateTConst t) r
toFOAS' (HO.FromIntegral t a) = FO.FromIntegral (translateType t) (toFOAS' a)
toFOAS' (HO.BoolLit b) = FO.BoolLit b

toFOAS' (HO.Equal    a b) = FO.Compare FO.EQU (toFOAS' a) (toFOAS' b)
toFOAS' (HO.NotEqual a b) = FO.Compare FO.NEQ (toFOAS' a) (toFOAS' b)
toFOAS' (HO.GTH      a b) = FO.Compare FO.GTH (toFOAS' a) (toFOAS' b)
toFOAS' (HO.LTH      a b) = FO.Compare FO.LTH (toFOAS' a) (toFOAS' b)
toFOAS' (HO.GTE      a b) = FO.Compare FO.GEQ (toFOAS' a) (toFOAS' b)
toFOAS' (HO.LTE      a b) = FO.Compare FO.LEQ (toFOAS' a) (toFOAS' b)

toFOAS' (HO.Unit) = FO.Unit

toFOAS' (HO.Tup2 a b) = FO.Tup2 (toFOAS' a) (toFOAS' b)
toFOAS' (HO.Fst a) = FO.Fst (toFOAS' a)
toFOAS' (HO.Snd a) = FO.Snd (toFOAS' a)

toFOAS' (HO.TupN t) = FO.TupN (HO.tupMap toFOAS' t)
toFOAS' (HO.GetN l n a) = FO.GetN l (HO.natToInt n) (toFOAS' a)

toFOAS' (HO.App f a) = FO.App (toFOAS' f) (toFOAS' a)
toFOAS' (HO.Lambda t f) = FO.Lambda v (translateType t) e
  where e = toFOAS' $ f (HO.Var v)
        v = getVar e

toFOAS' (HO.Let a f) = FO.Let v e1 e2
  where e1 = toFOAS' a
        e2 = toFOAS' $ f (HO.Var v)
        v = max (getVar e1) (getVar e2)

toFOAS' (HO.Return a) = FO.Return (toFOAS' a)
toFOAS' (HO.Bind a f) = FO.Bind (toFOAS' a) (toFOAS' f)

toFOAS' (HO.If cond th el) = FO.If (toFOAS' cond) (toFOAS' th) (toFOAS' el)

toFOAS' (HO.Rec f a) = FO.Rec (toFOAS' f) (toFOAS' a)

toFOAS' (HO.IterateWhile cond step init) =
  FO.IterateWhile
    (toFOAS' cond)
    (toFOAS' step)
    (toFOAS' init)
toFOAS' (HO.WhileM cond step action init) =
  FO.WhileM
    (toFOAS' cond)
    (toFOAS' step)
    (toFOAS' action)
    (toFOAS' init)

toFOAS' (HO.RunMutableArray a) = FO.RunMutableArray (toFOAS' a)
toFOAS' (HO.ReadIArray a b) = FO.ReadIArray (toFOAS' a) (toFOAS' b)
toFOAS' (HO.ArrayLength a) = FO.ArrayLength (toFOAS' a)

toFOAS' (HO.NewArray _ a) = FO.NewArray (toFOAS' a)
toFOAS' (HO.ReadArray a b) = FO.ReadArray  (toFOAS' a) (toFOAS' b)
toFOAS' (HO.WriteArray a b c) = FO.WriteArray (toFOAS' a) (toFOAS' b) (toFOAS' c)

toFOAS' (HO.ParM n f) = FO.ParM (toFOAS' n) (toFOAS' f)
toFOAS' (HO.Skip) = FO.Skip
toFOAS' (HO.Print a) = FO.Print (toFOAS' a)


toFOAST :: HO.Expr a -> FOT.Expr
toFOAST (HO.Binop op a b) =
  case op of
    HO.Plus  -> FOT.BinOp FO.Plus  (toFOAST a) (toFOAST b)
    HO.Minus -> FOT.BinOp FO.Minus (toFOAST a) (toFOAST b)
    HO.Mult  -> FOT.BinOp FO.Mult  (toFOAST a) (toFOAST b)
    HO.Quot  -> FOT.BinOp FO.Quot  (toFOAST a) (toFOAST b)
    HO.Rem   -> FOT.BinOp FO.Rem   (toFOAST a) (toFOAST b)
    HO.Div   -> FOT.BinOp FO.Div   (toFOAST a) (toFOAST b)
    HO.Mod   -> FOT.BinOp FO.Mod   (toFOAST a) (toFOAST b)
    HO.FDiv  -> FOT.BinOp FO.FDiv  (toFOAST a) (toFOAST b)
    HO.And   -> FOT.BinOp FO.And   (toFOAST a) (toFOAST b)
    HO.Or    -> FOT.BinOp FO.Or    (toFOAST a) (toFOAST b)
    HO.Min   -> FOT.BinOp FO.Min   (toFOAST a) (toFOAST b)
    HO.Max   -> FOT.BinOp FO.Max   (toFOAST a) (toFOAST b)
toFOAST (HO.Abs a)    = FOT.UnOp FO.Abs    (toFOAST a)
toFOAST (HO.Signum a) = FOT.UnOp FO.Signum (toFOAST a)
toFOAST (HO.Recip a)  = FOT.UnOp FO.Recip  (toFOAST a)
toFOAST (HO.FromInteger  t i) = FOT.FromInteger (translateTConst t) i
toFOAST (HO.FromRational t r) = FOT.FromRational (translateTConst t) r
toFOAST (HO.FromIntegral t a) = FOT.FromIntegral (translateType t) (toFOAST a)
toFOAST (HO.BoolLit b) = FOT.BoolLit b

toFOAST (HO.Equal    a b) = FOT.Compare FO.EQU (toFOAST a) (toFOAST b)
toFOAST (HO.NotEqual a b) = FOT.Compare FO.NEQ (toFOAST a) (toFOAST b)
toFOAST (HO.GTH      a b) = FOT.Compare FO.GTH (toFOAST a) (toFOAST b)
toFOAST (HO.LTH      a b) = FOT.Compare FO.LTH (toFOAST a) (toFOAST b)
toFOAST (HO.GTE      a b) = FOT.Compare FO.GEQ (toFOAST a) (toFOAST b)
toFOAST (HO.LTE      a b) = FOT.Compare FO.LEQ (toFOAST a) (toFOAST b)

toFOAST (HO.Unit) = FOT.Unit

toFOAST (HO.Tup2 a b) = FOT.Tup2 (toFOAST a) (toFOAST b)
toFOAST (HO.Fst a) = FOT.Fst (toFOAST a)
toFOAST (HO.Snd a) = FOT.Snd (toFOAST a)

toFOAST (HO.TupN t) = FOT.TupN (HO.tupMap toFOAST t)
toFOAST (HO.GetN l n a) = FOT.GetN l (HO.natToInt n) (toFOAST a)

toFOAST (HO.App f a) = FOT.App (toFOAST f) (toFOAST a)
toFOAST (HO.Lambda t f) = FOT.Lambda v (translateType t) e
  where e = toFOAST $ f (HO.Var v)
        v = getVarT e

toFOAST (HO.Let a f) = FOT.Let v e1 e2
  where e1 = toFOAST a
        e2 = toFOAST $ f (HO.Var v)
        v = max (getVarT e1) (getVarT e2)

toFOAST (HO.Return a) = FOT.Return (toFOAST a)
toFOAST (HO.Bind a f) = FOT.Bind (toFOAST a) (toFOAST f)

toFOAST (HO.If cond th el) = FOT.If (toFOAST cond) (toFOAST th) (toFOAST el)

toFOAST (HO.Rec f a) = FOT.Rec (toFOAST f) (toFOAST a)

toFOAST (HO.IterateWhile cond step init) =
  FOT.IterateWhile
    (toFOAST cond)
    (toFOAST step)
    (toFOAST init)
toFOAST (HO.WhileM cond step action init) =
  FOT.WhileM
    (toFOAST cond)
    (toFOAST step)
    (toFOAST action)
    (toFOAST init)

toFOAST (HO.RunMutableArray a) = FOT.RunMutableArray (toFOAST a)
toFOAST (HO.ReadIArray a b) = FOT.ReadIArray (toFOAST a) (toFOAST b)
toFOAST (HO.ArrayLength a) = FOT.ArrayLength (toFOAST a)

toFOAST (HO.NewArray t a) = FOT.NewArray (translateType t) (toFOAST a)
toFOAST (HO.ReadArray a b) = FOT.ReadArray  (toFOAST a) (toFOAST b)
toFOAST (HO.WriteArray a b c) = FOT.WriteArray (toFOAST a) (toFOAST b) (toFOAST c)

toFOAST (HO.ParM n f) = FOT.ParM (toFOAST n) (toFOAST f)
toFOAST (HO.Skip) = FOT.Skip
toFOAST (HO.Print a) = FOT.Print (toFOAST a)

getVarT :: FOT.Expr -> Int
getVarT = FOT.exprFold getVarT' max max3 max4

getVarT' :: (FOT.Expr -> Int) -> FOT.Expr -> Int
getVarT' f (FOT.Lambda i _ _) = i+1
getVarT' f (FOT.Let i _ _) = i+1
getVarT' f e | FOT.isAtomic e = 0
             | otherwise      = f e


getVar :: FO.Expr -> Int
getVar = FO.exprFold getVar' max max3 max4

getVar' :: (FO.Expr -> Int) -> FO.Expr -> Int
getVar' f (FO.Lambda i _ _) = i+1
getVar' f (FO.Let i _ _) = i+1
getVar' f e | isAtomic e = 0
            | otherwise  = f e

max3 :: Ord a => a -> a -> a -> a
max3 = reducel3 max

max4 :: Ord a => a -> a -> a -> a -> a
max4 = reducel4 max

