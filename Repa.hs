{-# OPTIONS_GHC -fth #-}
{-# LANGUAGE GADTs, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
module Repa where


import Data.Array.IO hiding (unsafeFreeze)
import Data.Array.MArray hiding (unsafeFreeze)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.Unsafe

import Control.Arrow
import Control.Monad
import Control.Monad.State

import System.IO.Unsafe

import Language.Haskell.TH


data Expr a where
  Var   :: Int -> Expr a
  Var2  :: Name -> Expr a
  Value :: a -> Expr a

  Binop :: Num a => Binop a -> Expr a -> Expr a -> Expr a
  Abs :: Num a => Expr a -> Expr a
  Signum :: Num a => Expr a -> Expr a
  FromInteger :: Num a => Integer -> Expr a

  Quot :: Integral a => Expr a -> Expr a -> Expr a
  Rem :: Integral a => Expr a -> Expr a -> Expr a

  And :: Expr Bool -> Expr Bool -> Expr Bool
  Or :: Expr Bool -> Expr Bool -> Expr Bool
  BoolLit :: Bool -> Expr Bool

  Equal :: Eq a => Expr a -> Expr a -> Expr Bool
  NotEqual :: Eq a => Expr a -> Expr a -> Expr Bool

  GTH :: Ord a => Expr a -> Expr a -> Expr Bool
  LTH :: Ord a => Expr a -> Expr a -> Expr Bool
  GTE :: Ord a => Expr a -> Expr a -> Expr Bool
  LTE :: Ord a => Expr a -> Expr a -> Expr Bool
  Min :: Ord a => Expr a -> Expr a -> Expr a
  Max :: Ord a => Expr a -> Expr a -> Expr a

  Tup2 :: Expr a -> Expr b -> Expr (a,b)
  Fst :: Expr (a,b) -> Expr a
  Snd :: Expr (a,b) -> Expr b

  Let :: Expr a -> (Expr a -> Expr b) -> Expr b

  Return :: Expr a -> Expr (IO a)
  Bind   :: Expr (IO a) -> (Expr a -> Expr (IO b)) -> Expr (IO b)

  IterateWhile :: (Expr s -> Expr Bool) -> (Expr s -> Expr s) -> Expr s -> Expr s
  WhileM :: (Expr s -> Expr Bool) -> (Expr s -> Expr s) -> (Expr s -> Expr (IO ())) -> Expr s -> Expr (IO ())

  RunMutableArray :: (MArray IOUArray a IO, IArray UArray a) => Expr (IO (IOUArray Int a)) -> Expr (UArray Int a)
  ReadIArray :: IArray UArray a => Expr (UArray Int a) -> Expr Int -> Expr a
  ArrayLength :: IArray UArray a => Expr (UArray Int a) -> Expr Int

  NewArray   :: MArray IOUArray a IO => Expr Int -> Expr (IO (IOUArray Int a))
  ReadArray  :: MArray IOUArray a IO => Expr (IOUArray Int a) -> Expr Int -> Expr (IO a)
  WriteArray :: MArray IOUArray a IO => Expr (IOUArray Int a) -> Expr Int -> Expr a -> Expr (IO ())
  ParM       :: Expr Int -> (Expr Int -> Expr (IO ())) -> Expr (IO ())
  Skip       :: Expr (IO ())

  Print :: Show a => Expr a -> Expr (IO ())



data FOExpr a where
  FOVar   :: Int -> FOExpr a
  --FOVar2  :: Name -> FOExpr a
  --FOValue :: a -> FOExpr a

  FOBinop :: BOP a -> FOExpr a -> FOExpr a -> FOExpr a
  FOAbs :: Num a => FOExpr a -> FOExpr a
  FOSignum :: Num a => FOExpr a -> FOExpr a
  FOFromInteger :: Num a => Integer -> FOExpr a

  FOBoolLit :: Bool -> FOExpr Bool

  FOCompare :: CompOp a -> FOExpr a -> FOExpr a -> FOExpr Bool

  FOTup2 :: FOExpr a -> FOExpr b -> FOExpr (a,b)
  FOFst :: FOExpr (a,b) -> FOExpr a
  FOSnd :: FOExpr (a,b) -> FOExpr b

  FOLet :: Int -> FOExpr a -> FOExpr b

  FOLambda :: Int -> FOExpr b -> FOExpr (a -> b)

  FOReturn :: FOExpr a -> FOExpr (IO a)
  FOBind   :: FOExpr (IO a) -> FOExpr (a -> IO b) -> FOExpr (IO b)

  FOIterateWhile :: FOExpr (s -> Bool) -> FOExpr (s -> s) -> FOExpr s -> FOExpr s
  FOWhileM :: FOExpr (s -> Bool) -> FOExpr (s -> s) -> FOExpr (s -> IO ()) -> FOExpr s -> FOExpr (IO ())

  FORunMutableArray :: (MArray IOUArray a IO, IArray UArray a) => FOExpr (IO (IOUArray Int a)) -> FOExpr (UArray Int a)
  FOReadIArray :: IArray UArray a => FOExpr (UArray Int a) -> FOExpr Int -> FOExpr a
  FOArrayLength :: IArray UArray a => FOExpr (UArray Int a) -> FOExpr Int

  FONewArray   :: MArray IOUArray a IO => FOExpr Int -> FOExpr (IO (IOUArray Int a))
  FOReadArray  :: MArray IOUArray a IO => FOExpr (IOUArray Int a) -> FOExpr Int -> FOExpr (IO a)
  FOWriteArray :: MArray IOUArray a IO => FOExpr (IOUArray Int a) -> FOExpr Int -> FOExpr a -> FOExpr (IO ())
  FOParM       :: FOExpr Int -> FOExpr (Int -> IO ()) -> FOExpr (IO ())
  FOSkip       :: FOExpr (IO ())

  FOPrint :: Show a => FOExpr a -> FOExpr (IO ())

deriving instance Show (FOExpr a)

data BOP a where
  BOPlus  :: Num a => BOP a
  BOMinus :: Num a => BOP a
  BOMult  :: Num a => BOP a
  BOQuot :: Integral a => BOP a
  BORem  :: Integral a => BOP a
  BOMin :: Ord a => BOP a
  BOMax :: Ord a => BOP a
  BOAnd :: BOP Bool
  BOOr  :: BOP Bool

deriving instance Show (BOP a)
deriving instance Eq (BOP a)

data CompOp a where
  Equ  :: Eq a => CompOp a
  NEqu :: Eq a => CompOp a
  GThn :: Ord a => CompOp a
  LThn :: Ord a => CompOp a
  GEqu :: Ord a => CompOp a
  LEqu :: Ord a => CompOp a

deriving instance Show (CompOp a)
deriving instance Eq (CompOp a)

data Binop a where
  Plus  :: Binop a
  Mult  :: Binop a
  Minus :: Binop a

deriving instance Eq (Binop a)

instance Num a => Num (Expr a) where
  (+) = Binop Plus
  (*) = Binop Mult
  (-) = Binop Minus
  abs = Abs
  signum = Signum
  fromInteger = FromInteger


data M a = M { unM :: forall b. ((a -> Expr (IO b)) -> Expr (IO b)) }

instance Monad M where
  return a = M $ \k -> k a
  M f >>= g = M $ \k -> f (\a -> unM (g a) k)

instance Functor M where
  fmap f (M g) = M (\k -> g (k . f))

runM :: M (Expr a) -> Expr (IO a)
runM (M f) = f Return

newArrayE :: MArray IOUArray a IO => Expr Int -> M (Expr (IOUArray Int a))
newArrayE i = M (\k -> NewArray i `Bind` k)

parM :: Expr Int -> (Expr Int -> M ()) -> M ()
parM l body = M (\k -> ParM l (\i -> unM (body i) (\() -> Skip))
                       `Bind` (\_ -> k ()))

writeArrayE :: MArray IOUArray a IO => Expr (IOUArray Int a) -> Expr Int -> Expr a -> M ()
writeArrayE arr i a = M (\k -> WriteArray arr i a `Bind` (\_ -> k ()))

readArrayE :: MArray IOUArray a IO => Expr (IOUArray Int a) -> Expr Int -> M (Expr a)
readArrayE arr i = M (\k -> ReadArray arr i `Bind` k)

readIArray :: IArray UArray a => Expr (UArray Int a) -> Expr Int -> Expr a
readIArray arr i = ReadIArray arr i

arrayLength :: IArray UArray a => Expr (UArray Int a) -> Expr Int
arrayLength arr = ArrayLength arr


--share :: Computable a =>  a -> M (a)
--share a = M (\k -> Return (internalize a) `Bind` k)

printE :: (Computable a, Show (Internal a)) => a -> M ()
printE a = M (\k -> Print (internalize a) `Bind` (\_ -> k ()))

whileE :: Computable st => (st -> Expr Bool) -> (st -> st) -> (st -> M ()) -> st -> M () -- a :: Expr (Internal st), action :: st -> M (), internalize :: st -> Expr (Internal st)
whileE cond step action init = M (\k -> WhileM (lowerFun cond) (lowerFun step) (\a -> unM ((action . externalize) a) (\() -> Skip)) (internalize init)
                                        `Bind` (\_ -> k ()))

runMutableArray :: (MArray IOUArray a IO, IArray UArray a) => M (Expr (IOUArray Int a)) -> Expr (UArray Int a)
runMutableArray m = RunMutableArray (runM m)

--Examples

fillArray :: MArray IOUArray a IO => Expr a -> Expr Int -> M (Expr (IOUArray Int a))
fillArray a l = do arr <- newArrayE l
                   parM l (\i ->
                            writeArrayE arr i a
                          )
                   return arr

-- Eval

eval :: Expr a -> a
eval (Value a) = a

eval (Binop Plus   a b) = (eval a) + (eval b)
eval (Binop Minus a b) = (eval a) - (eval b)
eval (Binop Mult  a b) = (eval a) * (eval b)
eval (Abs a) = abs (eval a)
eval (Signum a) = signum (eval a)
eval (FromInteger i) = fromInteger i

eval (Equal a b) = (eval a) == (eval b)
eval (NotEqual a b) = (eval a) /= (eval b)

eval (LTH a b) = (eval a) <  (eval b)
eval (LTE a b) = (eval a) <= (eval b)
eval (GTH a b) = (eval a) >  (eval b)
eval (GTE a b) = (eval a) >= (eval b)

eval (Max a b) = max (eval a) (eval b)
eval (Min a b) = min (eval a) (eval b)

eval (Tup2 a b) = (eval a, eval b)
eval (Fst a) = fst (eval a)
eval (Snd a) = snd (eval a)

eval (Return a) = return (eval a)
eval (Bind m f) = (eval m) >>= (\a -> eval $ f (Value a))

eval (IterateWhile  cond step init) = while (evalFun cond) (evalFun step) (eval init)
eval (WhileM cond step action init) = whileM (evalFun cond) (evalFun step) (evalFun action) (eval init)

eval (RunMutableArray arr) = unsafePerformIO (eval arr >>= unsafeFreeze)
eval (ReadIArray arr i)    = (eval arr) ! (eval i)
eval (ArrayLength arr)     = (snd $ bounds (eval arr)) + 1

eval (NewArray l)         = newArray_ (0, (eval l)-1)
eval (ReadArray arr i)    = readArray  (eval arr) (eval i)
eval (WriteArray arr i a) = writeArray (eval arr) (eval i) (eval a)

eval (ParM i body) = forM_ [0..(eval (i-1))] (\i -> eval (body (Value i)))
eval (Skip)        = return ()
eval (Print a)     = print (eval a)

eval (Let e f) = evalFun f (eval e)

evalFun :: (Expr a -> Expr b) -> a -> b
evalFun f = eval . f . Value

while cond step s | cond s    = while cond step (step s)
                  | otherwise = s

whileM :: Monad m => (a -> Bool) -> (a -> a) -> (a -> m ()) ->  a -> m ()
whileM cond step action s | cond s    = action s >> whileM cond step action (step s)
                          | otherwise = return ()

showExpr :: Int -> Expr a -> String
showExpr i (Var v) = "x" ++ (show v)
showExpr i (Binop op a b)  = "(" ++ (showBinOp i op a b) ++ ")"
showExpr i (Abs a)         = "(abs " ++ (showExpr i a) ++ ")"
showExpr i (Signum a)      = "(signum " ++ (showExpr i a) ++ ")"
showExpr i (FromInteger n) = show n
showExpr i (BoolLit b)     = show b
showExpr i (Equal a b)     = "(" ++ (showExpr i a) ++ " == " ++ (showExpr i b) ++ ")"
showExpr i (NotEqual a b)     = "(" ++ (showExpr i a) ++ " /= " ++ (showExpr i b) ++ ")"
showExpr i (LTH a b)     = "(" ++ (showExpr i a) ++ " < " ++ (showExpr i b) ++ ")"
showExpr i (LTE a b)     = "(" ++ (showExpr i a) ++ " <= " ++ (showExpr i b) ++ ")"
showExpr i (GTH a b)     = "(" ++ (showExpr i a) ++ " > " ++ (showExpr i b) ++ ")"
showExpr i (GTE a b)     = "(" ++ (showExpr i a) ++ " >= " ++ (showExpr i b) ++ ")"
showExpr i (Max a b)     = "(max " ++ (showExpr i a) ++ " " ++ (showExpr i b) ++ ")"
showExpr i (Min a b)     = "(min " ++ (showExpr i a) ++ " " ++ (showExpr i b) ++ ")"
showExpr i (Tup2 a b)    = "(" ++ (showExpr i a) ++ ", " ++ (showExpr i b) ++ ")"
showExpr i (Fst a) = "(fst " ++ (showExpr i a) ++ ")"
showExpr i (Snd a) = "(snd " ++ (showExpr i a) ++ ")"
showExpr i (Return a)      = "(return " ++ (showExpr i a) ++ ")"
showExpr i (Bind m f)      = "(" ++ (showExpr i m) ++ " >>= " ++ (showExprFun i f) ++ ")"
showExpr i (RunMutableArray arr) = "(runMutableArray " ++ (showExpr i arr) ++ ")"
showExpr i (ReadIArray arr ix)   = "(readIArray " ++ (showExpr i arr) ++ " " ++ (showExpr i ix) ++ ")"
showExpr i (ArrayLength arr)     = "(arrayLength " ++ (showExpr i arr) ++ ")"
showExpr i (NewArray l)          = "(newArray " ++ (showExpr i l) ++ ")"
showExpr i (ReadArray arr ix)    = "(readArray " ++ (showExpr i arr) ++ " " ++ (showExpr i ix) ++ ")"
showExpr i (WriteArray arr ix a) = "(writeArray " ++ (showExpr i arr) ++ " " ++ (showExpr i ix) ++ " " ++ (showExpr i a) ++ ")"
showExpr i (ParM n f) = "(parM " ++ (showExpr i n) ++ " " ++ (showExprFun i f) ++ ")"
showExpr i Skip = "skip"
showExpr i (Print a) = "(print " ++ (showExpr i a) ++ ")"
showExpr i (Let e f) = "(let x" ++ (show i) ++ " = " ++ (showExpr (i+1) e) ++ " in " ++ (showExpr (i+1) (f (Var i))) ++ ")"


showExprFun :: Int -> (Expr a -> Expr b) -> String
showExprFun i f = "(\\x" ++ (show i) ++ " -> " ++ (showExpr (i+1) (f (Var i))) ++ ")"


showBinOp :: Int -> Binop a -> Expr a -> Expr a -> String
showBinOp i Minus a b = (showExpr i a) ++ " - " ++ (showExpr i b)
showBinOp i Plus  a b = (showExpr i a) ++ " + " ++ (showExpr i b)
showBinOp i Mult  a b = (showExpr i a) ++ " * " ++ (showExpr i b)


translate :: Expr a -> Q Exp
translate (Var2 n) = return $ VarE n

translate (BoolLit b) = [| b |]

translate (Binop op a b) =
  case op of
       Plus   -> [| $(e1) + $(e2) |]
       Minus -> [| $(e1) - $(e2) |]
       Mult  -> [| $(e1) * $(e2) |]
  where e1 = translate a
        e2 = translate b
translate (Abs a) = [| abs $(translate a) |]
translate (Signum a) = [| signum $(translate a) |]
translate (FromInteger n) = [| n |]

translate (Equal a b) = [| $(translate a) == $(translate b) |]
translate (NotEqual a b) = [| $(translate a) /= $(translate b) |]

translate (LTH a b) = [| $(translate a) <  $(translate b) |]
translate (LTE a b) = [| $(translate a) <= $(translate b) |]
translate (GTH a b) = [| $(translate a) >  $(translate b) |]
translate (GTE a b) = [| $(translate a) >= $(translate b) |]

translate (Max a b) = [| max $(translate a) $(translate b) |]
translate (Min a b) = [| min $(translate a) $(translate b) |]

translate (Tup2 a b) = [| ($(translate a), $(translate b)) |]
translate (Fst a) = [| fst $(translate a) |]
translate (Snd a) = [| snd $(translate a) |]

translate (Return a) = [|return $(translate a)|]
translate (Bind m f) = [| $(translate m)  >>= $(trans f) |]

translate (RunMutableArray arr) = [| unsafePerformIO ($(translate arr) >>= unsafeFreeze) |]

translate (NewArray l)          = [| newIOUArray (0, $(translate (l-1))) |]
translate (ReadArray arr ix)    = [| readArray $(translate arr) $(translate ix) |]
translate (WriteArray arr ix a) = [| writeArray $(translate arr) $(translate ix) $(translate a) |]
translate (ParM n f) = [| forM_ [0..($(translate (n-1)))] $(translateFunction f) |]
translate (IterateWhile cond step init) = [| while $(trans cond) $(trans step) $(translate init) |]
translate (WhileM cond step action init) = [| whileM $(trans cond) $(trans step) $(trans action) $(translate init) |]
translate Skip       = [| return () |]
translate (Print a)  = [| print $(translate a) |]

translateFunction :: (Expr a -> Expr b) -> Q Exp
translateFunction f =
  do x <- newName "x"
     fbody <- translate (f (Var2 x))
     return $ LamE [VarP x] fbody

newIOUArray :: MArray IOUArray a IO => (Int, Int) -> IO (IOUArray Int a)
newIOUArray = newArray_


class Computable a where
  type Internal a
  internalize :: a -> Expr (Internal a)
  externalize :: Expr (Internal a) -> a


instance Computable (Expr a) where
  type Internal (Expr a) = a
  internalize = id
  externalize = id

instance (Computable a, Computable b) => Computable (a, b) where
  type Internal (a,b) = (Internal a, Internal b)
  internalize (a,b) = Tup2 (internalize a) (internalize b)
  externalize a = (externalize (Fst a), externalize (Snd a))

iterateWhile :: Computable st => (st -> Expr Bool) -> (st -> st) -> st -> st
iterateWhile cond step init = externalize $ IterateWhile (lowerFun cond) (lowerFun step) (internalize init)


lowerFun :: (Computable a, Computable b) => (a -> b) -> Expr (Internal a) -> Expr (Internal b)
lowerFun f = internalize . f . externalize

lowerFun2 :: (Computable a, Computable b, Computable c) => (a -> b -> c) -> Expr (Internal a) -> Expr (Internal b) -> Expr (Internal c)
lowerFun2 f a b = internalize $ f (externalize a) (externalize b)

liftFun :: (Computable a, Computable b) => (Expr (Internal a) -> Expr (Internal b)) -> a -> b
liftFun f = externalize . f . internalize

liftFun2 :: (Computable a, Computable b, Computable c) => (Expr (Internal a) -> Expr (Internal b) -> Expr (Internal c)) -> a -> b -> c
liftFun2 f a b = externalize $ f (internalize a) (internalize b)

let_ :: (Computable a, Computable b) => a -> (a -> b) -> b
let_ a f = externalize (Let (internalize a) (lowerFun f))

class Trans a where
  trans :: a -> Q Exp

instance Trans (Expr a) where
  trans = translate

instance (Computable a, Computable b) => Trans (a,b) where
  trans = translate . internalize

instance (Computable a, Trans b) => Trans (a -> b) where
  trans f = do
    x <- newName "x"
    fbody <- trans (f (externalize (Var2 x)))
    return $ LamE [VarP x] fbody



toFOAS :: Expr a -> FOExpr a
toFOAS = toFOAS' 0

toFOAS' :: Int -> Expr a -> FOExpr a
toFOAS' i (Var v) = FOVar v

toFOAS' i (Binop op a b) =
  case op of
    Plus  -> FOBinop BOPlus  (toFOAS' i a) (toFOAS' i b)
    Minus -> FOBinop BOMinus (toFOAS' i a) (toFOAS' i b)
    Mult  -> FOBinop BOMult  (toFOAS' i a) (toFOAS' i b)
toFOAS' i (Abs a) = FOAbs (toFOAS' i a)
toFOAS' i (Signum a) = FOSignum (toFOAS' i a)
toFOAS' i (FromInteger n) = FOFromInteger n

toFOAS' i (Quot a b) = FOBinop BOQuot (toFOAS' i a) (toFOAS' i b)
toFOAS' i (Rem  a b) = FOBinop BORem  (toFOAS' i a) (toFOAS' i b)
toFOAS' i (And  a b) = FOBinop BOAnd  (toFOAS' i a) (toFOAS' i b)
toFOAS' i (Or   a b) = FOBinop BOOr   (toFOAS' i a) (toFOAS' i b)
toFOAS' i (Min  a b) = FOBinop BOMin  (toFOAS' i a) (toFOAS' i b)
toFOAS' i (Max  a b) = FOBinop BOMax  (toFOAS' i a) (toFOAS' i b)

toFOAS' i (Equal    a b) = FOCompare Equ  (toFOAS' i a) (toFOAS' i b)
toFOAS' i (NotEqual a b) = FOCompare NEqu (toFOAS' i a) (toFOAS' i b)
toFOAS' i (GTH      a b) = FOCompare GThn (toFOAS' i a) (toFOAS' i b)
toFOAS' i (LTH      a b) = FOCompare LThn (toFOAS' i a) (toFOAS' i b)
toFOAS' i (GTE      a b) = FOCompare GEqu (toFOAS' i a) (toFOAS' i b)
toFOAS' i (LTE      a b) = FOCompare LEqu (toFOAS' i a) (toFOAS' i b)

toFOAS' i (Tup2 a b) = FOTup2 (toFOAS' i a) (toFOAS' i b)
toFOAS' i (Fst a) = FOFst (toFOAS' i a)
toFOAS' i (Snd a) = FOSnd (toFOAS' i a)

toFOAS' i (Let a f) = FOLet i (toFOAS' (i+1) (f (Var i)))

toFOAS' i (Return a) = FOReturn (toFOAS' i a)
toFOAS' i (Bind a f) = FOBind (toFOAS' i a) (toFOASFun i f)

toFOAS' i (IterateWhile cond step init) =
  FOIterateWhile
    (toFOASFun i cond)
    (toFOASFun i step)
    (toFOAS' i init)
toFOAS' i (WhileM cond step action init) =
  FOWhileM
    (toFOASFun i cond)
    (toFOASFun i step)
    (toFOASFun i action)
    (toFOAS' i init)

toFOAS' i (RunMutableArray a) = FORunMutableArray (toFOAS' i a)
toFOAS' i (ReadIArray a b) = FOReadIArray (toFOAS' i a) (toFOAS' i b)
toFOAS' i (ArrayLength a) = FOArrayLength (toFOAS' i a)

toFOAS' i (NewArray a) = FONewArray (toFOAS' i a)
toFOAS' i (ReadArray a b) = FOReadArray  (toFOAS' i a) (toFOAS' i b)
toFOAS' i (WriteArray a b c) = FOWriteArray (toFOAS' i a) (toFOAS' i b) (toFOAS' i c)

toFOAS' i (ParM n f) = FOParM (toFOAS' i n) (toFOASFun i f)
toFOAS' i (Skip) = FOSkip
toFOAS' i (Print a) = FOPrint (toFOAS' i a)

toFOASFun :: Int -> (Expr a -> Expr b) -> FOExpr (a -> b)
toFOASFun i f = FOLambda i $ toFOAS' (i+1) $ f (Var i)


isAtomic :: FOExpr a -> Bool
isAtomic (FOVar _)         = True
isAtomic (FOFromInteger _) = True
isAtomic (FOBoolLit _)     = True
isAtomic (FOSkip)          = True
isAtomic _ = False

