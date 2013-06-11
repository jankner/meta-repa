{-# LANGUAGE GADTs #-}
module Core where

import FOASTyped (reducel3,reducel4,isAtomic)
import qualified FOASTyped as FO
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
toFOAS (HO.Var v) = FO.Var v
toFOAS (HO.Binop t op a b) =
  case op of
    HO.Plus  -> FO.BinOp (translateType t) FO.Plus  (toFOAS a) (toFOAS b)
    HO.Minus -> FO.BinOp (translateType t) FO.Minus (toFOAS a) (toFOAS b)
    HO.Mult  -> FO.BinOp (translateType t) FO.Mult  (toFOAS a) (toFOAS b)
    HO.Quot  -> FO.BinOp (translateType t) FO.Quot  (toFOAS a) (toFOAS b)
    HO.Rem   -> FO.BinOp (translateType t) FO.Rem   (toFOAS a) (toFOAS b)
    HO.Div   -> FO.BinOp (translateType t) FO.Div   (toFOAS a) (toFOAS b)
    HO.Mod   -> FO.BinOp (translateType t) FO.Mod   (toFOAS a) (toFOAS b)
    HO.FDiv  -> FO.BinOp (translateType t) FO.FDiv  (toFOAS a) (toFOAS b)
    HO.And   -> FO.BinOp (translateType t) FO.And   (toFOAS a) (toFOAS b)
    HO.Or    -> FO.BinOp (translateType t) FO.Or    (toFOAS a) (toFOAS b)
    HO.Min   -> FO.BinOp (translateType t) FO.Min   (toFOAS a) (toFOAS b)
    HO.Max   -> FO.BinOp (translateType t) FO.Max   (toFOAS a) (toFOAS b)
    HO.Xor   -> FO.BinOp (translateType t) FO.Xor   (toFOAS a) (toFOAS b)
    HO.BAnd  -> FO.BinOp (translateType t) FO.BAnd  (toFOAS a) (toFOAS b)
    HO.BOr   -> FO.BinOp (translateType t) FO.BOr   (toFOAS a) (toFOAS b)
toFOAS (HO.Unop t op a) =
  case op of
    HO.Abs        -> FO.UnOp (translateType t) FO.Abs        (toFOAS a)
    HO.Signum     -> FO.UnOp (translateType t) FO.Signum     (toFOAS a)
    HO.Recip      -> FO.UnOp (translateType t) FO.Recip      (toFOAS a)
    HO.Complement -> FO.UnOp (translateType t) FO.Complement (toFOAS a)
    HO.Exp        -> FO.UnOp (translateType t) FO.Exp        (toFOAS a)
    HO.Sqrt       -> FO.UnOp (translateType t) FO.Sqrt       (toFOAS a)
    HO.Log        -> FO.UnOp (translateType t) FO.Log        (toFOAS a)
    HO.Sin        -> FO.UnOp (translateType t) FO.Sin        (toFOAS a)
    HO.Cos        -> FO.UnOp (translateType t) FO.Cos        (toFOAS a)
    HO.Tan        -> FO.UnOp (translateType t) FO.Tan        (toFOAS a)
    HO.ASin       -> FO.UnOp (translateType t) FO.ASin       (toFOAS a)
    HO.ACos       -> FO.UnOp (translateType t) FO.ACos       (toFOAS a)
    HO.ATan       -> FO.UnOp (translateType t) FO.ATan       (toFOAS a)
toFOAS (HO.FromInteger  t i) = FO.FromInteger (translateType t) i
toFOAS (HO.FromRational t r) = FO.FromRational (translateType t) r
toFOAS (HO.FromIntegral t t' a) = FO.FromIntegral (translateType t) (translateType t') (toFOAS a)
toFOAS (HO.BoolLit b) = FO.BoolLit b

toFOAS (HO.Bit t i) = FO.Bit (translateType t) (toFOAS i)
toFOAS (HO.Rotate t a i) = FO.Rotate (translateType t) (toFOAS a) (toFOAS i)
toFOAS (HO.ShiftL t a i) = FO.ShiftL (translateType t) (toFOAS a) (toFOAS i)
toFOAS (HO.ShiftR t a i) = FO.ShiftR (translateType t) (toFOAS a) (toFOAS i)
toFOAS (HO.PopCnt t a)   = FO.PopCnt (translateType t) (toFOAS a)

toFOAS (HO.Equal    t a b) = FO.Compare (translateType t) FO.EQU (toFOAS a) (toFOAS b)
toFOAS (HO.NotEqual t a b) = FO.Compare (translateType t) FO.NEQ (toFOAS a) (toFOAS b)
toFOAS (HO.GTH      t a b) = FO.Compare (translateType t) FO.GTH (toFOAS a) (toFOAS b)
toFOAS (HO.LTH      t a b) = FO.Compare (translateType t) FO.LTH (toFOAS a) (toFOAS b)
toFOAS (HO.GTE      t a b) = FO.Compare (translateType t) FO.GEQ (toFOAS a) (toFOAS b)
toFOAS (HO.LTE      t a b) = FO.Compare (translateType t) FO.LEQ (toFOAS a) (toFOAS b)

toFOAS (HO.Unit) = FO.Unit

toFOAS (HO.Tup2 a b) = FO.Tup2 (toFOAS a) (toFOAS b)
toFOAS (HO.Fst t a) = FO.Fst (translateType t) (toFOAS a)
toFOAS (HO.Snd t a) = FO.Snd (translateType t) (toFOAS a)

toFOAS (HO.TupN t) = FO.TupN (HO.tupMap toFOAS t)
toFOAS (HO.GetN t n a) = FO.GetN (translateType t) (HO.natToInt n) (toFOAS a)

toFOAS (HO.App f t a) = FO.App (toFOAS f) (translateType t) (toFOAS a)
toFOAS (HO.Lambda t f) = FO.Lambda v (translateType t) e
  where e = toFOAS $ f (HO.Var v)
        v = getVar e

toFOAS (HO.Let a f) = FO.Let v e1 e2
  where e1 = toFOAS a
        e2 = toFOAS $ f (HO.Var v)
        v = max (getVar e1) (getVar e2)

toFOAS (HO.Return t a) = FO.Return (translateType t) (toFOAS a)
toFOAS (HO.Bind t a f) = FO.Bind (translateType t) (toFOAS a) (toFOAS f)

toFOAS (HO.If cond th el) = FO.If (toFOAS cond) (toFOAS th) (toFOAS el)

toFOAS (HO.Rec t f a) = FO.Rec (translateType t) (toFOAS f) (toFOAS a)

toFOAS (HO.IterateWhile t cond step init) =
  FO.IterateWhile
    (translateType t)
    (toFOAS cond)
    (toFOAS step)
    (toFOAS init)
toFOAS (HO.WhileM t cond step action init) =
  FO.WhileM
    (translateType t)
    (toFOAS cond)
    (toFOAS step)
    (toFOAS action)
    (toFOAS init)

toFOAS (HO.RunMutableArray a) = FO.RunMutableArray (toFOAS a)
toFOAS (HO.ReadIArray t a b) = FO.ReadIArray (translateType t) (toFOAS a) (toFOAS b)
toFOAS (HO.ArrayLength a) = FO.ArrayLength (toFOAS a)

toFOAS (HO.NewArray t a) = FO.NewArray (translateType t) (toFOAS a)
toFOAS (HO.ReadArray a b) = FO.ReadArray (toFOAS a) (toFOAS b)
toFOAS (HO.WriteArray t a b c) = FO.WriteArray (translateType t) (toFOAS a) (toFOAS b) (toFOAS c)

toFOAS (HO.ParM n f) = FO.ParM (toFOAS n) (toFOAS f)
toFOAS (HO.Skip) = FO.Skip
toFOAS (HO.Print a) = FO.Print (toFOAS a)

getVar :: FO.Expr -> Int
getVar = FO.exprFold getVar' max max3 max4

getVar' :: (FO.Expr -> Int) -> FO.Expr -> Int
getVar' f (FO.Lambda i _ _) = i+1
getVar' f (FO.Let i _ _) = i+1
getVar' f e | isAtomic e = 0
            | otherwise      = f e


max3 :: Ord a => a -> a -> a -> a
max3 = reducel3 max

max4 :: Ord a => a -> a -> a -> a -> a
max4 = reducel4 max

