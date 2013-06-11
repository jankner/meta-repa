{-# OPTIONS_GHC -fth #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module FOASTyped 
  ( Expr(..)
  , translateW
  , translateU
  , cse
  , exprTraverse
  , exprTraverse0
  , exprFold
  , isAtomic
  , reducel3
  , reducel4
  , showVar
  ) where

import FOASCommon
import Types
import Eval

import qualified Data.Vector.Unboxed as VU
import qualified Data.Vector.Unboxed.Mutable as VU hiding (length)

import Data.Bits

import Data.Int
import Data.Word
import Data.List
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Maybe
import Data.Ratio

import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import qualified Language.Haskell.TH as TH
import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Lib

import GHC.Prim
import GHC.Exts
import GHC.Real
import GHC.Int
import GHC.Word



data Expr =
  -- Int -> a
    Var Int
  -- P a -> a -> a -> a
  | BinOp Type BinOp Expr Expr
  -- P a -> a -> a
  | UnOp Type UnOp Expr
  -- Num a => Integer -> a
  | FromInteger Type Integer
  -- Fractional a => Rational -> a
  | FromRational Type Rational
  -- (Integral a, Num b) => a -> b
  | FromIntegral Type Type Expr

  -- (Bits a) => Int -> a
  | Bit Type Expr
  -- (Bits a) => a -> Int -> a
  | Rotate Type Expr Expr
  -- (Bits a) => a -> Int -> a
  | ShiftL Type Expr Expr
  -- (Bits a) => a -> Int -> a
  | ShiftR Type Expr Expr
  -- (Bits a) => a -> Int
  | PopCnt Type Expr

  -- Bool -> Bool
  | BoolLit Bool

  -- CompOp a -> a -> a -> Bool
  | Compare Type CompOp Expr Expr

  | Unit
  
  -- a -> b -> (a,b)
  | Tup2 Expr Expr
  -- (a,b) -> a
  | Fst Type Expr
  -- (a,b) -> b
  | Snd Type Expr

  -- [a1..an] -> (a1,..an)
  | TupN [Expr]

  -- n -> i-> (a1,..ai,..an) -> ai
  | GetN Type Int Expr
  
  -- Int -> a -> b -> b
  | Let Int Expr Expr

  | LetAnn Int Type Expr Expr
  
  -- (a -> b) -> a -> b
  | App Expr Type Expr
  -- Int -> b -> (a -> b)
  | Lambda Int Type Expr
  
  -- a -> IO a
  | Return Type Expr
  -- IO a -> (a -> IO b) -> IO b
  | Bind Type Expr Expr

  -- Bool -> a -> a -> a
  | If Expr Expr Expr
  
  -- ((a -> r) -> a -> r) -> a -> r
  | Rec Type Expr Expr
  -- (s -> Bool) -> (s -> s) -> s -> s
  | IterateWhile Type Expr Expr Expr
  -- (s -> Bool) -> (s -> s) -> (s -> IO ()) -> s -> (IO ())
  | WhileM Type Expr Expr Expr Expr
  
  -- (MArray IOUArray a IO, IArray UArray a) => (IO (IOUArray Int a)) -> (UArray Int a)
  | RunMutableArray Expr
  -- IArray UArray a => (UArray Int a) -> Int -> a
  | ReadIArray Type Expr Expr
  -- IArray UArray a => (UArray Int a) -> Int
  | ArrayLength Expr
  
  -- MArray IOUArray a IO => Int -> (IO (IOUArray Int a))
  | NewArray Type Expr
  -- MArray IOUArray a IO => (IOUArray Int a) -> Int -> (IO a)
  | ReadArray Expr Expr
  -- MArray IOUArray a IO => (IOUArray Int a) -> Int -> a -> (IO ())
  | WriteArray Type Expr Expr Expr
  -- Int -> (Int -> IO ()) -> (IO ())
  | ParM Expr Expr
  -- (IO ())
  | Skip
  
  -- Show a => a -> (IO ())
  | Print Expr


-- Alpha renaming

type RenameEnv = IM.IntMap Int
type RenameState = Int

type Rename a = Reader (IM.IntMap Int, Int) a

runRename m = runReader m (IM.empty, 0)

canonicalAlphaRename :: Expr -> Expr
canonicalAlphaRename e = e' --trace ("rena: " ++ (show e')) $ trace ("show: " ++ (show e)) e'
  where e' = runRename $ exprTraverse0 rename e

lookVar :: Int -> Rename (Maybe Int)
lookVar v = reader (IM.lookup v . fst)

nextVar :: Rename Int
nextVar = reader snd

addVar v m = do
  v' <- nextVar
  a <- local (\(env,next) -> (IM.insert v next env, next+1)) m
  return (v',a)

rename :: (Expr -> Rename Expr) -> Expr -> Rename Expr
rename k (Var v) = do
  mv <- lookVar v --reader (lookup v)
  case mv of
    Just v' -> return (Var v')
    Nothing -> return (Var v)
rename k (Let v e1 e2) = do
  e1' <- rename k e1
  (v',e2') <- addVar v (rename k e2)
  return (Let v' e1' e2')
rename k (Lambda v t e) = do
  (v',e') <- addVar v (rename k e)
  return (Lambda v' t e')
rename k e | isAtomic e = return e
           | otherwise  = k e

-- Comparison


instance Eq Expr where
  e1 == e2 = canonicalAlphaRename e1 `eq` canonicalAlphaRename e2

eq (Var v1)                   (Var v2)                   = v1 == v2
eq (BinOp t1 op1 a1 b1)       (BinOp t2 op2 a2 b2)       = t1 == t2 && op1 == op2 && a1 `eq` a2 && b1 `eq` b2
eq (Compare t1 op1 a1 b1)     (Compare t2 op2 a2 b2)     = t1 == t2 && op1 == op2 && a1 `eq` a2 && b1 `eq` b2
eq (UnOp t1 op1 a1)           (UnOp t2 op2 a2)           = t1 == t2 && op1 == op2 && a1 `eq` a2
eq (FromInteger t1 i1)        (FromInteger t2 i2)        = t1 == t2 && i1 == i2
eq (FromRational t1 r1)       (FromRational t2 r2)       = t1 == t2 && r1 == r2
eq (FromIntegral t1 _ a1)     (FromIntegral t2 _ a2)     = t1 == t2 && a1 `eq` a2
eq (BoolLit b1)               (BoolLit b2)               = b1 == b2
eq (Bit t1 a1)                (Bit t2 a2)                = t1 == t2 && a1 `eq` a2 
eq (Rotate t1 a1 b1)          (Rotate t2 a2 b2)          = t1 == t2 && a1 `eq` a2 && b1 `eq` b2
eq (ShiftL t1 a1 b1)          (ShiftL t2 a2 b2)          = t1 == t2 && a1 `eq` a2 && b1 `eq` b2
eq (ShiftR t1 a1 b1)          (ShiftR t2 a2 b2)          = t1 == t2 && a1 `eq` a2 && b1 `eq` b2
eq (PopCnt t1 a1)             (PopCnt t2 a2)             = t1 == t2 && a1 `eq` a2
eq (Tup2 a1 b1)               (Tup2 a2 b2)               = a1 `eq` a2 && b1 `eq` b2
eq (Fst t1 a1)                (Fst t2 a2)                = t1 == t2 && a1 `eq` a2
eq (Snd t1 a1)                (Snd t2 a2)                = t1 == t2 && a1 `eq` a2
eq (TupN as1)                 (TupN as2)                 = foldl1 (&&) (zipWith eq as1 as2)
eq (GetN t1 i1 a1)            (GetN t2 i2 a2)            = t1 == t2 && i1 == i2 && a1 `eq` a2
eq (Let v1 a1 b1)             (Let v2 a2 b2)             = v1 == v2 && a1 `eq` a2 && b1 `eq` b2 
eq (App a1 t1 b1)             (App a2 t2 b2)             = a1 `eq` a2 && t1 == t2 && b1 `eq` b2 
eq (Lambda v1 t1 a1)          (Lambda v2 t2 a2)          = v1 == v2 && t1 == t2 && a1 `eq` a2
eq (Return t1 a1)             (Return t2 a2)             = t1 == t2 && a1 `eq` a2
eq (Bind t1 a1 b1)            (Bind t2 a2 b2)            = t1 == t2 && a1 `eq` a2 && b1 `eq` b2
eq (If a1 b1 c1)              (If a2 b2 c2)              = a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2
eq (Rec _ a1 b1)              (Rec _ a2 b2)              = a1 `eq` a2 && b1 `eq` b2 
eq (IterateWhile t1 a1 b1 c1) (IterateWhile t2 a2 b2 c2) = t1 == t2 && a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2
eq (WhileM t1 a1 b1 c1 d1)    (WhileM t2 a2 b2 c2 d2)    = t1 == t2 && a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2 && d1 `eq` d2
eq (RunMutableArray a1)       (RunMutableArray a2)       = a1 `eq` a2
eq (ReadIArray t1 a1 b1)      (ReadIArray t2 a2 b2)      = t1 == t2 && a1 `eq` a2 && b1 `eq` b2
eq (ArrayLength a1)           (ArrayLength a2)           = a1 `eq` a2
eq (NewArray t1 a1)           (NewArray t2 a2)           = t1 == t2 && a1 `eq` a2
eq (ReadArray a1 b1)          (ReadArray a2 b2)          = a1 `eq` a2 && b1 `eq` b2
eq (WriteArray t1 a1 b1 c1)   (WriteArray t2 a2 b2 c2)   = t1 == t2 && a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2
eq (ParM a1 b1)               (ParM a2 b2)               = a1 `eq` a2 && b1 `eq` b2
eq (Unit)                     (Unit)                     = True
eq (Skip)                     (Skip)                     = True
eq (Print a1)                 (Print a2)                 = a1 `eq` a2
eq _                          _                          = False


instance Ord Expr where
  compare a b = cmp (canonicalAlphaRename a) (canonicalAlphaRename b)

infix  4 `cmp`
infixr 3 `lexi`

lexi :: Ordering -> Ordering -> Ordering
lexi EQ o2 = o2
lexi o1 _  = o1

cmpList :: [Expr] -> [Expr] -> Ordering
cmpList []     []     = EQ
cmpList []     (_:_)  = LT
cmpList (_:_)  []     = GT
cmpList (x:xs) (y:ys) =
  case cmp x y of
    EQ -> cmpList xs ys
    o  -> o
  
cmp (Var v1)                   (Var v2)                   = compare v1 v2
cmp (BinOp t1 op1 a1 b1)       (BinOp t2 op2 a2 b2)       = compare t1 t2 `lexi` compare op1 op2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (Compare t1 op1 a1 b1)     (Compare t2 op2 a2 b2)     = compare t1 t2 `lexi` compare op1 op2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (UnOp t1 op1 a1)           (UnOp t2 op2 a2)           = compare t1 t2 `lexi` compare op1 op2 `lexi` a1 `cmp` a2
cmp (FromInteger t1 i1)        (FromInteger t2 i2)        = compare t1 t2 `lexi` compare i1 i2
cmp (FromRational t1 r1)       (FromRational t2 r2)       = compare t1 t2 `lexi` compare r1 r2
cmp (FromIntegral t1 _ a1)     (FromIntegral t2 _ a2)     = compare t1 t2 `lexi` a1 `cmp` a2
cmp (BoolLit b1)               (BoolLit b2)               = compare b1 b2
cmp (Bit t1 a1)                (Bit t2 a2)                = compare t1 t2 `lexi` a1 `cmp` a2 
cmp (Rotate t1 a1 b1)          (Rotate t2 a2 b2)          = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (ShiftL t1 a1 b1)          (ShiftL t2 a2 b2)          = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (ShiftR t1 a1 b1)          (ShiftR t2 a2 b2)          = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (PopCnt t1 a1)             (PopCnt t2 a2)             = compare t1 t2 `lexi` a1 `cmp` a2
cmp (Tup2 a1 b1)               (Tup2 a2 b2)               = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (Fst t1 a1)                (Fst t2 a2)                = compare t1 t2 `lexi` a1 `cmp` a2
cmp (Snd t1 a1)                (Snd t2 a2)                = compare t1 t2 `lexi` a1 `cmp` a2
cmp (TupN as1)                 (TupN as2)                 = cmpList as1 as2
cmp (GetN t1 i1 a1)            (GetN t2 i2 a2)            = compare t1 t2 `lexi` compare i1 i2 `lexi` a1 `cmp` a2
cmp (Let v1 a1 b1)             (Let v2 a2 b2)             = compare v1 v2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2 
cmp (App a1 t1 b1)             (App a2 t2 b2)             = a1 `cmp` a2 `lexi` compare t1 t2 `lexi` b1 `cmp` b2 
cmp (Lambda v1 t1 a1)          (Lambda v2 t2 a2)          = compare v1 v2 `lexi` compare t1 t2 `lexi` a1 `cmp` a2
cmp (Return t1 a1)             (Return t2 a2)             = compare t1 t2 `lexi` a1 `cmp` a2
cmp (Bind t1 a1 b1)            (Bind t2 a2 b2)            = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (If a1 b1 c1)              (If a2 b2 c2)              = a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2
cmp (Rec _ a1 b1)              (Rec _ a2 b2)              = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (IterateWhile t1 a1 b1 c1) (IterateWhile t2 a2 b2 c2) = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2
cmp (WhileM t1 a1 b1 c1 d1)    (WhileM t2 a2 b2 c2 d2)    = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2 `lexi` d1 `cmp` d2
cmp (RunMutableArray a1)       (RunMutableArray a2)       = a1 `cmp` a2
cmp (ReadIArray t1 a1 b1)      (ReadIArray t2 a2 b2)      = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (ArrayLength a1)           (ArrayLength a2)           = a1 `cmp` a2
cmp (NewArray t1 a1)           (NewArray t2 a2)           = compare t1 t2 `lexi` a1 `cmp` a2
cmp (ReadArray a1 b1)          (ReadArray a2 b2)          = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (WriteArray t1 a1 b1 c1)   (WriteArray t2 a2 b2 c2)   = compare t1 t2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2
cmp (ParM a1 b1)               (ParM a2 b2)               = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (Skip)                     (Skip)                     = EQ
cmp (Print a1)                 (Print a2)                 = a1 `cmp` a2
cmp e1 e2                                                 = compare (exprOrd e1) (exprOrd e2)

exprOrd :: Expr -> Int
exprOrd (Var _)                = 1
exprOrd (BinOp _ _ _ _)        = 2
exprOrd (Compare _ _ _ _)      = 3
exprOrd (UnOp _ _ _)           = 4
exprOrd (FromInteger _ _)      = 5
exprOrd (FromRational _ _)     = 6
exprOrd (FromIntegral _ _ _)   = 7
exprOrd (BoolLit _)            = 8
exprOrd (Tup2 _ _)             = 9
exprOrd (Fst _ _)              = 10
exprOrd (Snd _ _)              = 11
exprOrd (TupN _)               = 12
exprOrd (GetN _ _ _)           = 13
exprOrd (Let _ _ _)            = 14
exprOrd (App _ _ _)            = 15
exprOrd (Lambda _ _ _)         = 16
exprOrd (Return _ _)           = 17
exprOrd (Bind _ _ _)           = 18
exprOrd (If _ _ _)             = 19
exprOrd (IterateWhile _ _ _ _) = 20
exprOrd (WhileM _ _ _ _ _)     = 21
exprOrd (RunMutableArray _)    = 22
exprOrd (ReadIArray _ _ _)     = 23
exprOrd (ArrayLength _)        = 24
exprOrd (NewArray _ _)         = 25
exprOrd (ReadArray _ _)        = 26
exprOrd (WriteArray _ _ _ _)   = 28
exprOrd (ParM _ _)             = 29
exprOrd (Unit)                 = 30
exprOrd (Skip)                 = 31
exprOrd (Print _)              = 32
exprOrd (Rec _ _ _)            = 33
exprOrd (Bit _ _)              = 34
exprOrd (Rotate _ _ _)         = 35
exprOrd (ShiftL _ _ _)         = 36
exprOrd (ShiftR _ _ _)         = 37
exprOrd (PopCnt _ _)           = 39

-- General traversal

exprFold :: ((Expr -> a) -> Expr -> a)
         -> (a -> a -> a)
         -> (a -> a -> a -> a)
         -> (a -> a -> a -> a -> a)
         -> Expr
         -> a
exprFold f g2 g3 g4 e = f (exprRec f g2 g3 g4) e

exprRec :: ((Expr -> a) -> Expr -> a)
        -> (a -> a -> a)
        -> (a -> a -> a -> a)
        -> (a -> a -> a -> a -> a)
        -> Expr
        -> a
exprRec f g2 g3 g4 e@(FromIntegral t s e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(UnOp t op e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Bit t e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(PopCnt t e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Fst t e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Snd t e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Return _ e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(NewArray _ e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(RunMutableArray e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(ArrayLength e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Print e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(GetN t n e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Lambda v t e1) = exprFold f g2 g3 g4 e1

exprRec f g2 g3 g4 e@(Rec t e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(App e1 t e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(BinOp t op e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Compare t op e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Rotate t e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ShiftL t e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ShiftR t e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Tup2 e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Let v e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Bind t e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ReadIArray t e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ReadArray e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ParM e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)

exprRec f g2 g3 g4 e@(If e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)
exprRec f g2 g3 g4 e@(IterateWhile t e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)
exprRec f g2 g3 g4 e@(WriteArray t e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)

exprRec f g2 g3 g4 e@(WhileM t e1 e2 e3 e4) = g4 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3) (exprFold f g2 g3 g4 e4)

exprRec f g2 g3 g4 e@(TupN es) = foldl1 g2 (map (exprFold f g2 g3 g4) es)

exprTraverse0 :: Monad m
              => ((Expr -> m Expr) -> Expr -> m Expr)
              -> Expr
              -> m Expr
exprTraverse0 f = liftM fst . exprTraverse f' (const id)
  where f' k = liftM (\x -> (x,())) . f (liftM fst . k)

exprTraverse :: Monad m
             => ((Expr -> m (Expr,a)) -> Expr -> m (Expr,a))
             -> (a -> a -> a)
             -> Expr
             -> m (Expr,a)
exprTraverse f g e = f (exprTrav f g) e

exprTrav :: Monad m
         => ((Expr -> m (Expr,a)) -> Expr -> m (Expr,a))
         -> (a -> a -> a)
         -> Expr
         -> m (Expr,a)
exprTrav f g e@(FromIntegral t s e1) = liftM ((FromIntegral t s) *** id) (exprTraverse f g e1)
exprTrav f g e@(UnOp t op e1) = liftM ((UnOp t op) *** id) (exprTraverse f g e1)
exprTrav f g e@(Bit t e1) = liftM ((Bit t) *** id) (exprTraverse f g e1)
exprTrav f g e@(PopCnt t e1) = liftM ((PopCnt t) *** id) (exprTraverse f g e1)
exprTrav f g e@(Fst t e1) = liftM ((Fst t) *** id) (exprTraverse f g e1)
exprTrav f g e@(Snd t e1) = liftM ((Snd t) *** id) (exprTraverse f g e1)
exprTrav f g e@(Lambda v t e1) = liftM ((Lambda v t) *** id) (exprTraverse f g e1)
exprTrav f g e@(Return t e1) = liftM ((Return t) *** id) (exprTraverse f g e1)
exprTrav f g e@(NewArray t e1) = liftM ((NewArray t) *** id) (exprTraverse f g e1)
exprTrav f g e@(RunMutableArray e1) = liftM (RunMutableArray *** id) (exprTraverse f g e1)
exprTrav f g e@(ArrayLength e1) = liftM (ArrayLength *** id) (exprTraverse f g e1)
exprTrav f g e@(Print e1) = liftM (Print *** id) (exprTraverse f g e1)
exprTrav f g e@(GetN t n e1) = liftM ((GetN t n) *** id) (exprTraverse f g e1)

exprTrav f g e@(Rec t e1 e2) = liftM2 ((Rec t) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(App e1 t e2) = liftM2 ((flip App t) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(BinOp t op e1 e2) = liftM2 ((BinOp t op) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Compare t op e1 e2) = liftM2 ((Compare t op) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Rotate t e1 e2) = liftM2 ((Rotate t) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ShiftL t e1 e2) = liftM2 ((ShiftL t) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ShiftR t e1 e2) = liftM2 ((ShiftR t) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Tup2 e1 e2) = liftM2 (Tup2 **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Let v e1 e2) = liftM2 ((Let v) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Bind t e1 e2) = liftM2 ((Bind t) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ReadIArray t e1 e2) = liftM2 ((ReadIArray t) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ReadArray e1 e2) = liftM2 (ReadArray **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ParM e1 e2) = liftM2 (ParM **** g) (exprTraverse f g e1) (exprTraverse f g e2)

exprTrav f g e@(If e1 e2 e3) = liftM3 (If ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)
exprTrav f g e@(IterateWhile t e1 e2 e3) = liftM3 ((IterateWhile t) ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)
exprTrav f g e@(WriteArray t e1 e2 e3) = liftM3 ((WriteArray t) ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)

exprTrav f g e@(WhileM t e1 e2 e3 e4) = liftM4 ((WhileM t) ****** (reducel4 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3) (exprTraverse f g e4)
exprTrav f g e@(TupN es) =
  do (es',as) <- liftM unzip $ mapM (exprTraverse f g) es
     return (TupN es', foldl1 g as)
exprTrav f g e = exprTraverse f g e


(****) :: (a -> b -> c) ->  (a' -> b' -> c') -> ((a,a') -> (b,b') -> (c,c'))
f **** g = \(a,a') (b,b') -> (f a b, g a' b')

(*****) :: (a -> b -> c -> d) ->  (a' -> b' -> c' -> d') -> ((a,a') -> (b,b') -> (c,c') -> (d,d'))
f ***** g = \(a,a') (b,b') (c,c') -> (f a b c, g a' b' c')

(******) :: (a -> b -> c -> d -> e) -> (a' -> b' -> c' -> d' -> e') -> ((a,a') -> (b,b') -> (c,c') -> (d,d') -> (e,e'))
f ****** g = \(a,a') (b,b') (c,c') (d,d') -> (f a b c d, g a' b' c' d')

reducel3 :: (a -> a -> a) -> a -> a -> a -> a
reducel3 f a b c = (a `f` b) `f` c

reducel4 :: (a -> a -> a) -> a -> a -> a -> a -> a
reducel4 f a b c d = ((a `f` b) `f` c) `f` d

isAtomic :: Expr -> Bool
isAtomic (Var _)            = True
isAtomic (FromInteger _ _)  = True
isAtomic (FromRational _ _) = True
isAtomic (BoolLit _)        = True
isAtomic (Skip)             = True
isAtomic (Unit)             = True
isAtomic _ = False

-- CSE

type UndoEnv = (IM.IntMap Expr, Int)

countVar :: Int -> Int -> Int
countVar new cur | new < 0x40000000 = new
                 | otherwise        = cur

undoSome :: IM.IntMap (Int,Int) -> Expr -> Expr
undoSome map e = runReader (exprTraverse0 (undoSome' map) e) (IM.empty, 0x3fffffff)

undoSome' :: IM.IntMap (Int,Int)
         -> (Expr -> Reader UndoEnv Expr)
         -> Expr
         -> Reader UndoEnv Expr
undoSome' map k (Var v) =
  reader $ \(emap,_) ->
    case IM.lookup v emap of
      Just e  -> e
      Nothing -> Var v
undoSome' map k (Lambda v t e) =
  do e' <- local (second (countVar v)) $ undoSome' map k e
     return (Lambda v t e')
undoSome' map k (Let v e1 e2) =
  local (second (countVar v)) $ 
    do e1' <- undoSome' map k e1
       b' <- reader snd
       case IM.lookup v map of
         Just (b,c) | b /= 0x3fffffff && c <= 1 && b == b' || not (worthIt 2 e1') ->
           do e2' <- local (first $ IM.insert v e1') $ undoSome' map k e2
              return e2'
         _ -> 
           do e2' <- undoSome' map k e2
              return (Let v e1' e2')
undoSome' map k e | isAtomic e = return e
                  | otherwise  = k e

worthIt :: Int -> Expr -> Bool
worthIt i (ParM _ _)     = True
worthIt i (IterateWhile _ _ _ _) = True
worthIt i (WhileM _ _ _ _ _) = True
worthIt i (Rec _ _ _) = True
worthIt i (RunMutableArray _) = True
worthIt i e = False

--worthIt :: Int -> Expr -> Bool
--worthIt i e | isAtomic e = False
--worthIt 0 e              = True
--worthIt i (Tup2 e1 e2)         = worthIt (i-2) e1 || worthIt (i-2) e2
--worthIt i (BinOp t op e1 e2)   = worthIt (i-1) e1 || worthIt (i-1) e2
--worthIt i (Compare t op e1 e2) = worthIt (i-1) e1 || worthIt (i-1) e2
--worthIt i (UnOp t op e)        = worthIt (i-1) e
--worthIt i (FromIntegral t s e) = worthIt (i-2) e
--worthIt i (Fst t e)            = worthIt (i-0) e
--worthIt i (Snd t e)            = worthIt (i-0) e
--worthIt i (GetN _ _ e)         = worthIt (i-0) e 
--worthIt i (Return t e)         = worthIt (i-1) e
--worthIt i (NewArray t e)       = worthIt i e
--worthIt i e = True


findMin :: IS.IntSet -> Maybe Int
findMin s | IS.null s = Nothing
          | otherwise  = Just (IS.findMin s)

minVar :: IS.IntSet -> Int
minVar = (fromMaybe 0x3fffffff) .  findMin 

type ExprInfo = (Int -- min (free vars in expression)
                ,Int -- count
                ,Int -- min (bound vars in expression scope)
                )

data CSEState = CSEState { exprMap :: IM.IntMap (M.Map Expr ExprInfo), varCounter :: Int }

newtype CSEM a = CSEM { unCSEM :: StateT CSEState (ReaderT [Int] (Writer (IM.IntMap (Int,Int)))) a }
  deriving (Monad, MonadReader [Int], MonadWriter (IM.IntMap (Int,Int)), MonadState CSEState)

runCSE :: CSEM a -> (a, CSEState, IM.IntMap (Int,Int))
runCSE m = (a, st, w)
  where ((a, st), w) = runWriter (runReaderT (runStateT (unCSEM m) startState) [])
        startState = CSEState {exprMap = IM.empty, varCounter = 0x40000000}

cse :: Expr -> Expr
cse e = eFinal
  where ((e',fvs), s, varMap) = runCSE (exprTraverse thing IS.union e)
        e'' = letBindExprs (exprMap s) e'
        varMap' = varMap `IM.union` (exprMapToVarMap (exprMap s))
        eFinal = undoSome varMap' e''

addEnvVar :: Int -> CSEM a -> CSEM a
addEnvVar v = local (v:)

getEnvVar :: CSEM Int
getEnvVar = reader r
 where r []    = 0x3fffffff
       r (x:_) = x

writeExprs :: IM.IntMap (M.Map Expr ExprInfo) -> CSEM ()
writeExprs exprMap = tell (exprMapToVarMap exprMap)

exprMapToVarMap :: IM.IntMap (M.Map Expr ExprInfo) -> IM.IntMap (Int,Int)
exprMapToVarMap exprMap = IM.fromList $ map (\(_,(_,(v,c,b))) -> (v,(b,c))) (exprMapToList exprMap)

thing :: (Expr -> CSEM (Expr,IS.IntSet)) -> Expr -> CSEM (Expr,IS.IntSet)
thing k (Var v) = return (Var v, IS.singleton v)
thing k (Let v e1 e2) = do
  (e2',vs2) <- addEnvVar v $ thing k e2
  st <- get
  let (exprs,newMap) = extractExprsLE (exprMap st) v
  let e2Final = letBindExprs exprs e2'
  put (st {exprMap = newMap})
  b <- getEnvVar
  writeExprs exprs
  (e1',vs1) <- thing k e1
  v1 <- addExpr e1' b vs1
  let vs' = IS.difference (IS.union vs1 vs2) (IS.singleton v)
  v' <- addExpr (Let v (Var v1) e2Final) b vs'
  return (Var v', vs')
thing k (Lambda v t e) = do
  (e',vs) <- addEnvVar v $ thing k e
  st <- get
  let (exprs,newMap) = extractExprsLE (exprMap st) v
  let eFinal = letBindExprs exprs e'
  put (st {exprMap = newMap})
  b <- getEnvVar
  writeExprs exprs
  let vs' = IS.difference vs (IS.singleton v)
  v' <- addExpr (Lambda v t eFinal) b vs'
  return (Var v', vs')
thing k e | isAtomic e = return (e, IS.empty)
thing k e | otherwise  = do
  (e',vs) <- k e
  b <- getEnvVar
  v <- addExpr e' b vs
  return (Var v, vs)


exprMapToList :: IM.IntMap (M.Map Expr ExprInfo) -> [(Int,(Expr,ExprInfo))]
exprMapToList exprMap = concatMap (uncurry mapToList) $ IM.toAscList exprMap

extractExprsLE :: IM.IntMap (M.Map Expr ExprInfo) -> Int -> (IM.IntMap (M.Map Expr ExprInfo), IM.IntMap (M.Map Expr ExprInfo))
extractExprsLE exprMap v = (lessEqExprs,newMap)
  where lessEqExprs = maybe restMap (\x -> IM.insert v x restMap) x
        (restMap, x, newMap) = IM.splitLookup v exprMap

mapToList :: Int -> M.Map Expr ExprInfo -> [(Int,(Expr,ExprInfo))]
mapToList i m = zip (repeat i) (M.toList m)

letBindExprs :: IM.IntMap (M.Map Expr ExprInfo) -> Expr -> Expr
letBindExprs exprMap e = foldl letBind e letExprs
  where letExprs = sortBy (\(_,(_,(v1,_,_))) (_,(_,(v2,_,_))) -> compare v2 v1) (exprMapToList exprMap)

letBind :: Expr -> (Int,(Expr,ExprInfo)) -> Expr
letBind e (_,(e',(v,_,_))) = Let v e' e


removeWithDefault :: Int -> a -> IM.IntMap a -> (a, IM.IntMap a)
removeWithDefault k a map = (fromMaybe a old, map')
  where (old, map') = IM.updateLookupWithKey (\_ _ -> Nothing) k map
 
addExpr :: Expr -> Int -> IS.IntSet -> CSEM Int
addExpr e b vs = do
  st <- get
  let l = minVar vs
  let map = exprMap st
  let subMap = IM.findWithDefault M.empty l map
  let (x,newSubMap) = M.insertLookupWithKey (\key _ (oldv,oldc,oldb) -> (oldv,oldc+1, min oldb b)) e (varCounter st, 1, b) subMap
  case x of
    Just (v,c,_) -> do
      put (st {exprMap = IM.insert l newSubMap map})
      return v --trace ("l: " ++ (show l) ++ ", v: " ++ (showVar v) ++ ", c: " ++ (show (c+1)) ++ "b: " ++ (show b ) ++ ", e: " ++ (show e)) $ 
    Nothing  -> do
      let v = varCounter st
      put (st {exprMap = IM.insert l newSubMap map, varCounter = v + 1})
      return v --trace ("l: " ++ (show l) ++ ", v: " ++ (showVar v) ++ ", e: " ++ (show e)) $ 


-- Show

instance Show Expr where
  showsPrec = showExpr

showExpr :: Int -> Expr -> ShowS
showExpr d (Var v) = showsVar v
showExpr d (UnOp t op a) =
  case op of
    Abs    -> showApp d "abs" [a]
    Signum -> showApp d "signum" [a]
    Recip  -> showApp d "recip" [a]
    Complement -> showApp d "complement" [a]
    Exp    -> showApp d "exp" [a]
    Sqrt   -> showApp d "sqrt" [a]
    Log    -> showApp d "log" [a]
    Sin    -> showApp d "sin" [a]
    Tan    -> showApp d "tan" [a]
    Cos    -> showApp d "cos" [a]
    ASin   -> showApp d "asin" [a]
    ATan   -> showApp d "atan" [a]
    ACos   -> showApp d "acos" [a]
showExpr d (BinOp t op a b)  = showBinOp d op a b
showExpr d (Compare t op a b) = showCompOp d op a b
showExpr d (FromInteger t n) = showParen (d > 0) $ shows n . showString " :: " . shows t
showExpr d (FromRational t r) =
  case t of
    (TConst TFloat)  -> shows (fromRational r :: Float)
    (TConst TDouble) -> shows (fromRational r :: Double)
showExpr d (FromIntegral t s a) = showApp d "fromIntegral" [a]
showExpr d (Bit t a) = showApp d "bit" [a]
showExpr d (Rotate t a b) = showApp d "rotate" [a,b]
showExpr d (ShiftL t a b) = showApp d "shiftL" [a,b]
showExpr d (ShiftR t a b) = showApp d "shiftR" [a,b]
showExpr d (PopCnt t a) = showApp d "popCount" [a]
showExpr d (BoolLit b)     = shows b
showExpr d (Unit) = showString "()"
showExpr d (Tup2 a b)    = showParen True $ showsPrec 0 a . showString ", " . showsPrec 0 b
showExpr d (Fst t a) = showApp d "fst" [a]
showExpr d (Snd t a) = showApp d "snd" [a]
showExpr d (TupN as) = showString "(" . showsTup as
showExpr d (GetN t n a) = showApp d ("get" ++ (show t) ++ "_" ++ (show n)) [a]
showExpr d (Return t a) = showApp d "return" [a]
showExpr d (Bind t m f) = showParen (d > 1) $ showsPrec 1 m . showString " >>= " . showsPrec 2 f
showExpr d (If cond a b) = showParen (d > 0) $ showString "if " . showsPrec 0 cond . showString " then " . showsPrec 0 a . showString " else " . showsPrec 0 b
showExpr d (Rec t f a) = showApp d "rec" [f,a]
showExpr d (IterateWhile t cond step init) = showApp d "iterateWhile" [cond,step,init]
showExpr d (WhileM t cond step action init) = showApp d "whileM" [cond,step,action,init]
showExpr d (RunMutableArray arr) = showApp d "runMutableArray" [arr]
showExpr d (ReadIArray t arr ix)   = showApp d "readIArray" [arr,ix]
showExpr d (ArrayLength arr)     = showApp d "arrayLength" [arr]
showExpr d (NewArray t l)        = showApp d "newArray" [l]
showExpr d (ReadArray arr ix)    = showApp d "readArray" [arr,ix]
showExpr d (WriteArray t arr ix a) = showApp d "writeArray" [arr,ix,a]
showExpr d (ParM n f) = showApp d "parM" [n,f]
showExpr d Skip = showString "skip"
showExpr d (Print a) = showApp d "print" [a]
showExpr d (Let v e1 e2) = showParen (d > 10) $ showString "let " . showsVar v . showString " = " . showsPrec 0 e1 . showString " in " . showsPrec 0 e2
showExpr d (LetAnn v t e1 e2) = showParen (d > 10) $ showString "let " . showsVar v . showString " :: " . shows t . showString " = " . showsPrec 0 e1 . showString " in " . showsPrec 0 e2
showExpr d (Lambda v t e) = showString "(\\" . showsVar v . showString " :: " . shows t . showString " -> " . showsPrec 0 e . showString ")"
showExpr d (App e1 t e2) = showApp d (showsPrec 10 e1 "") [e2]

showsTup (a:[]) = showsPrec 0 a . showString ")"
showsTup (a:as) = showsPrec 0 a . showString "," . showsTup as

showApp :: Int -> String -> [Expr] -> ShowS
showApp d f es = showParen (d > 10) $ showString f . foldr1 (.) (map ((showString " " .) . showsPrec 11) es)

showsVar :: Int -> ShowS
showsVar v | v < 0x40000000 = showString "x" . shows v
           | otherwise      = showString "y" . shows (v - 0x40000000)

showVar v = showsVar v ""


-- Translation

--type Env = [(Int,Type)]

lookEnv :: Env -> Int -> Maybe Type
lookEnv = flip lookup

translateW :: Type -> Expr -> Q Exp
translateW t e = wrapValue t (translateU [] e)

translateU :: Env -> Expr -> Q Exp
translateU env (Var v) = return $ tupExpr [] (showVar v) t
  where t = case lookEnv env v of
              Just t  -> t
              Nothing -> error ("unknown var: " ++ showVar v)
translateU env (UnOp t op e) = translateUnOpU t op (translateU env e)
translateU env (BinOp t op e1 e2) = translateBinOpU t op (translateU env e1) (translateU env e2)
translateU env (FromInteger t i) = translateFromIntegerU t i
translateU env (FromRational t (a :% b)) = translateFromRationalU t (a :% b)
translateU env (FromIntegral t s e) = 
  caseE [| fromIntegral $(wrapValue s (translateU env e)) |]
    [match (return $ typeToPatternB "f" t) (normalB $ return $ tupExpr [] "f" t) []]
translateU env (Bit t e) = unwrap t [| bit (I# $(translateU env e)) |]
translateU env (Rotate t e1 e2) = unwrap t [| rotate $(wrapValue t (translateU env e1)) (I# $(translateU env e2)) |]
translateU env (ShiftL t e1 e2) = unwrap t [| shiftL $(wrapValue t (translateU env e1)) (I# $(translateU env e2)) |]
translateU env (ShiftR t e1 e2) = unwrap t [| shiftR $(wrapValue t (translateU env e1)) (I# $(translateU env e2)) |]
translateU env (PopCnt t e1) = unwrap tInt [| popCount $(wrapValue t (translateU env e1)) |]
translateU env (BoolLit b) = [| b |]
translateU env (Compare t op e1 e2) = translateCompOpU t op (translateU env e1) (translateU env e2)
translateU env (Unit) = [| () |]
translateU env (Tup2 e1 e2) = unboxedTupE [translateU env e1, translateU env e2]
translateU env (Fst t e) = translateGet env (GetN t 0 e)
translateU env (Snd t e) = translateGet env (GetN t 1 e)
translateU env (TupN es) = unboxedTupE (map (translateU env) es)
translateU env e@(GetN t i _) = translateGet env e
translateU env e@(App e1 t e2) = do
  let (e',es,args) = translateApp 0 [] e
  e'' <- translateU env e'
  let e''' = foldl AppE e'' args
  es' <- mapM (\(i,e,t) -> translateU env e) es
  let decs = zipWith (\(i,e,t) e' -> expToDec ("t" ++ (show i)) t e') es es'
  letE (map return decs) $
    return e'''
translateU env (LetAnn v t e1 e2) = do
  e1' <- translateU env e1
  let dec = expToDec (showVar v) t e1'
  r <- letE [return $ dec] $
    translateU ((v,t):env) e2
  return r
translateU env e@(Lambda v t e1) = sigE (translateLambdasU env [] e) (translateTypeUQ t)
translateU env (Return t e) = letE
  [valD (return (typeToPattern "w" t)) (normalB $ translateU env e) []]
  [| return $(return (typeToExpB "w" t)) |]
translateU env (Bind t e1 e2) = [| $(translateU env e1) >>= $wrap|]
  where wrap = lamE [return $ typeToPatternB "w" t] (makeApp "w" t (translateU env e2))
translateU env (If e1 e2 e3) = [| if $(translateU env e1) then $(translateU env e2) else $(translateU env e3) |]
translateU env (Rec t e1 e2) = do
  loopN <- newName "loop"
  letE [
    funD loopN $ [clause (map return (flatPat "a" t))
      (normalB (makeApp "a" t ((translateU env e1) `appE` (varE loopN)))) []]]
    (letBindAndApply "init" t (varE loopN) (translateU env e2))
translateU env (IterateWhile t cond step init) = do
  loopN <- newName "loop"
  initN <- newName "init"
  letE [
    funD loopN $ [clause (map return (flatPat "s" t)) (guardedB
      [ mamb2mab (normalG (makeApp "s" t (translateU env cond)), letBindAndApply "step" t (varE loopN) (makeApp "s" t (translateU env step)))
      , mamb2mab (normalG [|True|], return $ tupExpr [] "s" t)
      ])
      []]]
    (letBindAndApply "init" t (varE loopN) (translateU env init))
translateU env (WhileM t cond step action init) = do
  loopN <- newName "loop"
  let condE = makeApp "s" t (translateU env cond)
  let nextE = letBindAndApply "next" t (varE loopN) (makeApp "s" t (translateU env step))
  let actionE = makeApp "s" t (translateU env action)
  letE [
    funD loopN $ [clause (map return (flatPat "s" t)) (guardedB
      [ mamb2mab (normalG condE, [| $actionE >> $nextE |] )
      , mamb2mab (normalG [| True |], [| return () |] )
      ])
      []]]
    (letBindAndApply "init" t (varE loopN) (translateU env init))
translateU env (RunMutableArray e) = [| runMutableArray $(translateU env e) |]
translateU env (ReadIArray t e1 e2) = unwrap t [| $(translateU env e1) `VU.unsafeIndex` $(wrapValue tInt (translateU env e2)) |]
translateU env (ArrayLength e) = unwrap tInt [| VU.length $(translateU env e) |]
translateU env (NewArray t e) = sigE [| VU.new $(wrapValue tInt (translateU env e)) |] (translateTypeUQ (TIO $ TMArr t))
translateU env (WriteArray t e1 e2 e3) = [| VU.unsafeWrite $(translateU env e1) $(wrapValue tInt (translateU env e2)) $(wrapValue t (translateU env e3)) |]
translateU env (ReadArray e1 e2) = [| VU.unsafeRead $(translateU env e1) $(wrapValue tInt (translateU env e2)) |]
translateU env (ParM e1 e2) = [| parM $(translateU env e1) $(translateU env e2) |]
translateU env Skip = [| return () |]
translateU env (Print e) = [| print $(translateU env e) |]
translateU env e = error (show e)

letBindAndApply :: String -> Type -> Q Exp -> Q Exp -> Q Exp
letBindAndApply n t e1 e2 = 
    (letE [valD (return $ typeToPattern "init" t) (normalB e2) []]
      (makeApp "init" t e1))

mamb2mab :: Monad m => (m a, m b) -> m (a,b)
mamb2mab = uncurry (liftM2 (,))

makeApp :: String -> Type -> Q Exp -> Q Exp
makeApp n (TConst TUnit) e = appE e (tupE [])
makeApp n t e = foldl appE e (map return $ flatApp n t)

translateLambdasU :: Env -> [(Int,Type)] -> Expr -> Q Exp
translateLambdasU env vs (Lambda v (TFun t _) e) = translateLambdasU ((v,t):env) ((v,t):vs) e
translateLambdasU env vs e = translateU env e >>= return . LamE (flatPats (reverse vs))

flatPats :: [(Int,Type)] -> [Pat]
flatPats []         = []
flatPats ((v,t):vs) = (flatPat (showVar v) t) ++ (flatPats vs)

flatPat :: String -> Type -> [Pat]
flatPat n (TTup2 t1 t2) = (flatPat (n ++ "_0") t1) ++ (flatPat (n ++ "_1") t2)
flatPat n (TTupN ts) = concat $ zipWith flatPat ns ts
  where ns = map (\i -> n ++ "_" ++ show i) [0..length ts] 
flatPat n t = [BangP $ VarP $ mkName n]

expToDec :: String -> Type -> Exp -> Dec
expToDec n t e = ValD (typeToPattern n t) (NormalB e) []

translateApp :: Int -> [(Int,Expr,Type)] -> Expr -> (Expr,[(Int,Expr,Type)],[Exp])
translateApp i es (App e1 t (Var v)) =
  let (e',es',args) = translateApp i es e1
      args' = args ++ (flatApp (showVar v) t)
  in (e',es',args')
translateApp i es (App e1 t e2) =
  let (e',es',args) = translateApp (i+1) ((i,e2,t):es) e1
      args' = args ++ (flatApp ("t" ++ show i) t)
  in (e',es',args')
translateApp i es e = (e,es,[])

flatApp :: String -> Type -> [Exp]
flatApp n (TTup2 t1 t2) = (flatApp (n ++ "_0") t1) ++ (flatApp (n ++ "_1") t2)
flatApp n (TTupN ts)    = concat $ zipWith flatApp ns ts
  where ns = map (\i -> n ++ "_" ++ show i) [0..length ts] 
flatApp n t = [(VarE (mkName n))]


translateGet :: Env -> Expr -> Q Exp
translateGet env e@(GetN t _ _) = do
  (n, m) <- translateGet' e []
  case m of
    Just (is, e) -> 
      caseE (translateU env e) 
        [match 
          (return $ matchTupElem "t" t is) 
          (normalB (return (tupExpr is "t" t))) []]
    Nothing      -> varE n

translateGet' :: Expr -> [Int] -> Q (Name, Maybe ([Int],Expr))
translateGet' (Fst t e)    is = translateGet' e (0:is)
translateGet' (Snd t e)    is = translateGet' e (1:is)
translateGet' (GetN t i e) is = translateGet' e (i:is)
translateGet' (Var v) is = return (varTupElem v is, Nothing)
translateGet' e is = do
  n <- newName "get"
  return (n, Just (is,e))

varTupElem :: Int -> [Int] -> Name
varTupElem v is = mkName ((showVar v) ++ "_" ++ (intercalate "_" $ map show is))

tupExpr :: [Int] -> String -> Type -> Exp
tupExpr []     n (TConst tc)   = VarE $ mkName n
tupExpr []     n (TFun t1 t2)  = VarE $ mkName n
tupExpr (0:is) n (TTup2 t1 t2) = tupExpr is n t1
tupExpr (1:is) n (TTup2 t1 t2) = tupExpr is n t2
tupExpr []     n (TTup2 t1 t2) = UnboxedTupE [tupExpr [] (n ++ "_0") t1, tupExpr [] (n ++ "_1") t2]
tupExpr (i:is) n (TTupN ts)    = tupExpr is n (ts !! i)
tupExpr []     n (TTupN ts)    = UnboxedTupE (zipWith (tupExpr []) ns ts)
  where ns = map (\i -> n ++ "_" ++ show i) [0..length ts] 
tupExpr []     n (TMArr t)     = VarE $ mkName n
tupExpr []     n (TIArr t)     = VarE $ mkName n
tupExpr []     n (TIO t)       = VarE $ mkName n
tupExpr is     n t             = error "tupExpr: invalid arguments"

matchTupElem :: String -> Type -> [Int] -> Pat
matchTupElem n (TTup2 t1 t2) (0:is) = UnboxedTupP [matchTupElem n t1 is, WildP]
matchTupElem n (TTup2 t1 t2) (1:is) = UnboxedTupP [WildP, matchTupElem n t2 is]
matchTupElem n (TTupN ts)    (i:is) = UnboxedTupP $ zipWith f [0..] ts
  where f j t | j == i    = matchTupElem (n ++ "_" ++ (show j)) t is
              | otherwise = WildP
matchTupElem n (TTup2 t1 t2) []     = typeToPattern n (TTup2 t1 t2)
matchTupElem n (TTupN ts)    []     = typeToPattern n (TTupN ts)
matchTupElem n t             []     = BangP $ VarP $ mkName n
matchTupElem n t is = error ("matchTupElem: invalid arguments: " ++ n ++ ": " ++ (show t) ++ " | " ++ (show is))

typeToExpB :: String -> Type -> Exp
typeToExpB b (TConst tc) = typeConstToExpB b tc
typeToExpB b (TFun  t1 t2) = VarE $ mkName b
typeToExpB b (TTup2 t1 t2) = TupE [typeToExpB (b ++ "_0") t1, typeToExpB (b ++ "_1") t2]
typeToExpB b (TTupN ts)    = TupE (zipWith typeToExpB bs ts)
  where bs = map (\i -> b ++ "_" ++ show i) [0..length ts] 
typeToExpB b (TMArr t) = VarE $ mkName b
typeToExpB b (TIArr t) = VarE $ mkName b
typeToExpB b (TIO   t) = VarE $ mkName b

typeConstToExpB :: String -> TypeConst -> Exp
typeConstToExpB b TInt    = ConE 'I# `AppE` (VarE (mkName b))
typeConstToExpB b TInt64  = ConE 'I# `AppE` (VarE (mkName b))
typeConstToExpB b TWord   = ConE 'W# `AppE` (VarE (mkName b))
typeConstToExpB b TWord64 = ConE 'W# `AppE` (VarE (mkName b))
typeConstToExpB b TFloat  = ConE 'F# `AppE` (VarE (mkName b))
typeConstToExpB b TDouble = ConE 'D# `AppE` (VarE (mkName b))
typeConstToExpB b TBool   = VarE $ mkName b
typeConstToExpB b TUnit   = TupE []

typeToPattern :: String -> Type -> Pat
typeToPattern b (TConst tc) = BangP $ VarP $ mkName b
typeToPattern b (TFun  t1 t2) = VarP $ mkName b
typeToPattern b (TTup2 t1 t2) = UnboxedTupP [typeToPattern (b ++ "_0") t1, typeToPattern (b ++ "_1") t2]
typeToPattern b (TTupN ts)    = UnboxedTupP (zipWith typeToPattern bs ts)
  where bs = map (\i -> b ++ "_" ++ show i) [0..length ts] 
typeToPattern b (TMArr t) = BangP $ VarP $ mkName b
typeToPattern b (TIArr t) = BangP $ VarP $ mkName b
typeToPattern b (TIO   t) = BangP $ VarP $ mkName b

typeToPatternB :: String -> Type -> Pat
typeToPatternB b (TConst tc) = typeConstToPatternB b tc
typeToPatternB b (TFun  t1 t2) = VarP $ mkName b
typeToPatternB b (TTup2 t1 t2) = TupP [typeToPatternB (b ++ "_0") t1, typeToPatternB (b ++ "_1") t2]
typeToPatternB b (TTupN ts)    = TupP (zipWith typeToPatternB bs ts)
  where bs = map (\i -> b ++ "_" ++ show i) [0..length ts] 
typeToPatternB b (TMArr t) = BangP $ VarP $ mkName b
typeToPatternB b (TIArr t) = BangP $ VarP $ mkName b
typeToPatternB b (TIO   t) = BangP $ VarP $ mkName b

typeConstToPatternB :: String -> TypeConst -> Pat
typeConstToPatternB b TInt    = ConP 'I# [(VarP (mkName b))]
typeConstToPatternB b TInt64  = ConP 'I# [(VarP (mkName b))]
typeConstToPatternB b TWord   = ConP 'W# [(VarP (mkName b))]
typeConstToPatternB b TWord64 = ConP 'W# [(VarP (mkName b))]
typeConstToPatternB b TFloat  = ConP 'F# [(VarP (mkName b))]
typeConstToPatternB b TDouble = ConP 'D# [(VarP (mkName b))]
typeConstToPatternB b TBool   = BangP $ VarP $ mkName b
typeConstToPatternB b TUnit   = TupP []

translateTypeConstUQ :: TypeConst -> Q TH.Type
translateTypeConstUQ = return . translateTypeConstU

translateTypeConstU :: TypeConst -> TH.Type
translateTypeConstU TInt    = ConT ''Int#
translateTypeConstU TInt64  = ConT ''Int#
translateTypeConstU TWord   = ConT ''Word#
translateTypeConstU TWord64 = ConT ''Word#
translateTypeConstU TFloat  = ConT ''Float#
translateTypeConstU TDouble = ConT ''Double#
translateTypeConstU TBool   = ConT ''Bool
translateTypeConstU TUnit   = TupleT 0

translateTypeUQ :: Type -> Q TH.Type
translateTypeUQ = return . translateTypeU


translateTypeU :: Type -> TH.Type
translateTypeU (TConst tc) = translateTypeConstU tc
translateTypeU (TFun  t1 t2) = foldr1 funT $ map translateTypeU $ (flattenType t1) ++ [t2]
 where funT t1 t2 = (ArrowT `AppT` t1) `AppT` t2
translateTypeU (TTup2 t1 t2) = UnboxedTupleT 2 `AppT` (translateTypeU t1) `AppT` (translateTypeU t2)
translateTypeU (TTupN ts) = foldl AppT (UnboxedTupleT $ length ts) (map translateTypeU ts)
translateTypeU (TMArr t) = (ConT ''VU.IOVector) `AppT` (translateType t)
translateTypeU (TIArr t) = (ConT ''VU.Vector) `AppT` (translateType t)
translateTypeU (TIO   t) = (ConT ''IO) `AppT` (translateType t)

flattenType :: Type -> [Type]
flattenType (TTup2 t1 t2) = (flattenType t1) ++ (flattenType t2)
flattenType (TTupN ts) = concatMap flattenType ts
flattenType t = [t]

translateFromIntegerU :: Type -> Integer -> Q Exp
translateFromIntegerU (TConst TInt)    i = litE (intPrimL i)
translateFromIntegerU (TConst TInt64)  i = litE (intPrimL i)
translateFromIntegerU (TConst TWord)   i = litE (wordPrimL i)
translateFromIntegerU (TConst TWord64) i = litE (wordPrimL i)
translateFromIntegerU (TConst TDouble) i = litE (doublePrimL (i :% 1))
translateFromIntegerU (TConst TFloat)  i = litE (floatPrimL  (i :% 1))
translateFromIntegerU t                _ = error ("fromInteger: unsupported type: " ++ show t)

translateFromRationalU :: Type -> Rational -> Q Exp
translateFromRationalU (TConst TDouble) r = litE (doublePrimL r)
translateFromRationalU (TConst TFloat)  r = litE (floatPrimL  r)
translateFromRationalU _                _ = error "fromRational: unsupported type"


translateUnOpU :: Type -> UnOp -> Q Exp -> Q Exp
translateUnOpU (TConst TWord)   Complement  q = [| not# $q |]
translateUnOpU (TConst TWord64) Complement  q = [| not# $q |]
translateUnOpU (TConst TFloat)  Exp  q = [|  expFloat# $q |]
translateUnOpU (TConst TFloat)  Sqrt q = [| sqrtFloat# $q |]
translateUnOpU (TConst TFloat)  Log  q = [|  logFloat# $q |]
translateUnOpU (TConst TFloat)  Sin  q = [|  sinFloat# $q |]
translateUnOpU (TConst TFloat)  Cos  q = [|  cosFloat# $q |]
translateUnOpU (TConst TFloat)  Tan  q = [|  tanFloat# $q |]
translateUnOpU (TConst TFloat)  ASin q = [| asinFloat# $q |]
translateUnOpU (TConst TFloat)  ACos q = [| acosFloat# $q |]
translateUnOpU (TConst TFloat)  ATan q = [| atanFloat# $q |]
translateUnOpU (TConst TDouble) Exp  q = [|  expDouble# $q |]
translateUnOpU (TConst TDouble) Sqrt q = [| sqrtDouble# $q |]
translateUnOpU (TConst TDouble) Log  q = [|  logDouble# $q |]
translateUnOpU (TConst TDouble) Sin  q = [|  sinDouble# $q |]
translateUnOpU (TConst TDouble) Cos  q = [|  cosDouble# $q |]
translateUnOpU (TConst TDouble) Tan  q = [|  tanDouble# $q |]
translateUnOpU (TConst TDouble) ASin q = [| asinDouble# $q |]
translateUnOpU (TConst TDouble) ACos q = [| acosDouble# $q |]
translateUnOpU (TConst TDouble) ATan q = [| atanDouble# $q |]
translateUnOpU t Abs         q = unwrap t [| abs $(wrapValue t q) |]
translateUnOpU t Signum      q = unwrap t [| signum $(wrapValue t q) |]
translateUnOpU t Recip       q = unwrap t [| recip $(wrapValue t q) |]
translateUnOpU t Complement  q = unwrap t [| complement $(wrapValue t q) |]
translateUnOpU t Exp         q = unwrap t [| exp $(wrapValue t q) |]
translateUnOpU t Sqrt        q = unwrap t [| sqrt $(wrapValue t q) |]
translateUnOpU t Log         q = unwrap t [| log $(wrapValue t q) |]
translateUnOpU t Sin         q = unwrap t [| sin $(wrapValue t q) |]
translateUnOpU t Cos         q = unwrap t [| cos $(wrapValue t q) |]
translateUnOpU t Tan         q = unwrap t [| tan $(wrapValue t q) |]
translateUnOpU t ASin        q = unwrap t [| asin $(wrapValue t q) |]
translateUnOpU t ACos        q = unwrap t [| acos $(wrapValue t q) |]
translateUnOpU t ATan        q = unwrap t [| atan $(wrapValue t q) |]
      
translateBinOpU :: Type -> BinOp -> Q Exp -> Q Exp -> Q Exp
translateBinOpU (TConst TInt)    Minus q1 q2 = [| $q1 -# $q2 |]
translateBinOpU (TConst TInt64)  Minus q1 q2 = [| $q1 -# $q2 |]
translateBinOpU (TConst TWord)   Minus q1 q2 = [| minusWord#  $q1 $q2 |]
translateBinOpU (TConst TWord64) Minus q1 q2 = [| minusWord#  $q1 $q2 |]
translateBinOpU (TConst TFloat)  Minus q1 q2 = [| minusFloat# $q1 $q2 |]
translateBinOpU (TConst TDouble) Minus q1 q2 = [| $q1 -## $q2 |]
translateBinOpU (TConst TInt)    Plus  q1 q2 = [| $q1 +#  $q2 |]
translateBinOpU (TConst TInt64)  Plus  q1 q2 = [| $q1 +#  $q2 |]
translateBinOpU (TConst TWord)   Plus  q1 q2 = [| plusWord#  $q1 $q2 |]
translateBinOpU (TConst TWord64) Plus  q1 q2 = [| plusWord#  $q1 $q2 |]
translateBinOpU (TConst TFloat)  Plus  q1 q2 = [| plusFloat# $q1 $q2 |]
translateBinOpU (TConst TDouble) Plus  q1 q2 = [| $q1 +## $q2 |]
translateBinOpU (TConst TInt)    Mult  q1 q2 = [| $q1 *#  $q2 |]
translateBinOpU (TConst TInt64)  Mult  q1 q2 = [| $q1 *#  $q2 |]
translateBinOpU (TConst TWord)   Mult  q1 q2 = [| timesWord#  $q1 $q2 |]
translateBinOpU (TConst TWord64) Mult  q1 q2 = [| timesWord#  $q1 $q2 |]
translateBinOpU (TConst TFloat)  Mult  q1 q2 = [| timesFloat# $q1 $q2 |]
translateBinOpU (TConst TDouble) Mult  q1 q2 = [| $q1 *## $q2 |]
translateBinOpU (TConst TInt)    Quot  q1 q2 = [| quotInt#  $q1 $q2 |]
translateBinOpU (TConst TWord)   Quot  q1 q2 = [| quotWord# $q1 $q2 |]
translateBinOpU (TConst TInt)    Rem   q1 q2 = [| remInt#   $q1 $q2 |]
translateBinOpU (TConst TWord)   Rem   q1 q2 = [| remWord#  $q1 $q2 |]
translateBinOpU (TConst TFloat)  FDiv  q1 q2 = [| divideFloat# $q1 $q2 |]
translateBinOpU (TConst TDouble) FDiv  q1 q2 = [| $q1 /## $q2 |]
translateBinOpU (TConst TFloat)  Pow   q1 q2 = [| powerFloat# $q1 $q2 |]
translateBinOpU (TConst TDouble) Pow   q1 q2 = [| $q1 **## $q2 |]
translateBinOpU (TConst TWord)   Xor   q1 q2 = [| xor#  $q1 $q2 |]
translateBinOpU (TConst TWord64) Xor   q1 q2 = [| xor#  $q1 $q2 |]
translateBinOpU (TConst TWord)   BAnd  q1 q2 = [| and#  $q1 $q2 |]
translateBinOpU (TConst TWord64) BAnd  q1 q2 = [| and#  $q1 $q2 |]
translateBinOpU (TConst TWord)   BOr   q1 q2 = [| or#  $q1 $q2 |]
translateBinOpU (TConst TWord64) BOr   q1 q2 = [| or#  $q1 $q2 |]
translateBinOpU t Minus q1 q2 = unwrap t [| $(wrapValue t q1) - $(wrapValue t q2) |]
translateBinOpU t Plus  q1 q2 = unwrap t [| $(wrapValue t q1) + $(wrapValue t q2) |]
translateBinOpU t Mult  q1 q2 = unwrap t [| $(wrapValue t q1) * $(wrapValue t q2) |]
translateBinOpU t Quot  q1 q2 = unwrap t [| $(wrapValue t q1) `quot` $(wrapValue t q2) |]
translateBinOpU t Rem   q1 q2 = unwrap t [| $(wrapValue t q1) `rem` $(wrapValue t q2) |]
translateBinOpU t Div   q1 q2 = unwrap t [| $(wrapValue t q1) `div` $(wrapValue t q2) |]
translateBinOpU t Mod   q1 q2 = unwrap t [| $(wrapValue t q1) `mod` $(wrapValue t q2) |]
translateBinOpU t FDiv  q1 q2 = unwrap t [| $(wrapValue t q1) / $(wrapValue t q2) |]
translateBinOpU t Min   q1 q2 = unwrap t [| min $(wrapValue t q1) $(wrapValue t q2) |]
translateBinOpU t Max   q1 q2 = unwrap t [| max $(wrapValue t q1) $(wrapValue t q2) |]
translateBinOpU t And   q1 q2 = unwrap t [| $(wrapValue t q1) && $(wrapValue t q2) |]
translateBinOpU t Or    q1 q2 = unwrap t [| $(wrapValue t q1) || $(wrapValue t q2) |]
translateBinOpU t Xor   q1 q2 = unwrap t [| $(wrapValue t q1) `xor` $(wrapValue t q2) |]
translateBinOpU t BAnd  q1 q2 = unwrap t [| $(wrapValue t q1) .&. $(wrapValue t q2) |]
translateBinOpU t BOr   q1 q2 = unwrap t [| $(wrapValue t q1) .|. $(wrapValue t q2) |]
translateBinOpU t Pow   q1 q2 = unwrap t [| $(wrapValue t q1) ** $(wrapValue t q2) |]

translateCompOpU :: Type -> CompOp -> Q Exp -> Q Exp -> Q Exp
translateCompOpU (TConst TInt)   EQU q1 q2 = [| $q1 ==# $q2 |]
translateCompOpU (TConst TInt)   NEQ q1 q2 = [| $q1 /=# $q2 |]
translateCompOpU (TConst TInt)   GTH q1 q2 = [| $q1 >#  $q2 |]
translateCompOpU (TConst TInt)   LTH q1 q2 = [| $q1 <#  $q2 |]
translateCompOpU (TConst TInt)   GEQ q1 q2 = [| $q1 >=# $q2 |]
translateCompOpU (TConst TInt)   LEQ q1 q2 = [| $q1 <=# $q2 |]
translateCompOpU (TConst TInt64) EQU q1 q2 = [| $q1 ==# $q2 |]
translateCompOpU (TConst TInt64) NEQ q1 q2 = [| $q1 /=# $q2 |]
translateCompOpU (TConst TInt64) GTH q1 q2 = [| $q1 >#  $q2 |]
translateCompOpU (TConst TInt64) LTH q1 q2 = [| $q1 <#  $q2 |]
translateCompOpU (TConst TInt64) GEQ q1 q2 = [| $q1 >=# $q2 |]
translateCompOpU (TConst TInt64) LEQ q1 q2 = [| $q1 <=# $q2 |]
translateCompOpU t EQU q1 q2 = [| $(wrapValue t q1) == $(wrapValue t q2) |]
translateCompOpU t NEQ q1 q2 = [| $(wrapValue t q1) /= $(wrapValue t q2) |]
translateCompOpU t GTH q1 q2 = [| $(wrapValue t q1) >  $(wrapValue t q2) |]
translateCompOpU t LTH q1 q2 = [| $(wrapValue t q1) <  $(wrapValue t q2) |]
translateCompOpU t GEQ q1 q2 = [| $(wrapValue t q1) >= $(wrapValue t q2) |]
translateCompOpU t LEQ q1 q2 = [| $(wrapValue t q1) <= $(wrapValue t q2) |]

--boxed to unboxed
unwrap :: Type -> Q Exp -> Q Exp
unwrap (TConst tc)     e = unwrapPrim tc e
unwrap t@(TFun t1 t2)  e = unwrapFun t e
unwrap t@(TTup2 t1 t2) e = letE [valD (return (typeToPatternB "w" t)) (normalB e) []] (unwrapVar "w" t)
unwrap t@(TTupN ts)    e = letE [valD (return (typeToPatternB "w" t)) (normalB e) []] (unwrapVar "w" t)
unwrap t               e = e

unwrapVar :: String -> Type -> Q Exp
unwrapVar b (TTup2 t1 t2)  = unboxedTupE [unwrapVar (b ++ "_0") t1, unwrapVar (b ++ "_1") t2]
unwrapVar b (TTupN ts)     = unboxedTupE $ zipWith unwrapVar bs ts
  where bs = map (\i -> b ++ "_" ++ show i) [0..length ts] 
unwrapVar b t@(TFun t1 t2) = unwrapFun t (varE (mkName b))
unwrapVar b (TConst TBool) = varE (mkName b)
unwrapVar b (TConst TUnit) = varE (mkName b)
unwrapVar b (TConst tc)    = varE (mkName b)
unwrapVar b t              = varE (mkName b)

unwrapFun :: Type -> Q Exp -> Q Exp
unwrapFun t e = lamE (map return (concat (zipWith flatPat ws args)))
                  (unwrap r (appsE (e : map return (zipWith typeToExpB ws args))))
  where ws = map (("wa"++) . show) [0..]
        (args, r) = argsAndResult t

unwrapPrim :: TypeConst -> Q Exp -> Q Exp
unwrapPrim TInt    e = [| case $e of (I# i) -> i|]
unwrapPrim TInt64  e = [| case $e of (I# i) -> i|]
unwrapPrim TWord   e = [| case $e of (W# i) -> i|]
unwrapPrim TWord64 e = [| case $e of (W# i) -> i|]
unwrapPrim TDouble e = [| case $e of (D# i) -> i|]
unwrapPrim TFloat  e = [| case $e of (F# i) -> i|]
unwrapPrim t       e = e

-- unboxed to boxed
wrapValue :: Type -> Q Exp -> Q Exp
wrapValue (TConst tc)     e = wrapPrim tc e
wrapValue t@(TFun t1 t2)  e = wrapFun t e
wrapValue t@(TTup2 t1 t2) e = letE [valD (return (typeToPattern "w" t)) (normalB e) []] (wrapVar "w" t)
wrapValue t@(TTupN ts)    e = letE [valD (return (typeToPattern "w" t)) (normalB e) []] (wrapVar "w" t)
wrapValue t               e = e

wrapVar :: String -> Type -> Q Exp
wrapVar b (TTup2 t1 t2)  = tupE [wrapVar (b ++ "_0") t1, wrapVar (b ++ "_1") t2]
wrapVar b (TTupN ts)     = tupE $ zipWith wrapVar bs ts
  where bs = map (\i -> b ++ "_" ++ show i) [0..length ts] 
wrapVar b t@(TFun t1 t2) = wrapFun t (varE (mkName b))
wrapVar b (TConst tc)    = wrapPrim tc (varE (mkName b))
wrapVar b t              = varE (mkName b)

wrapFun :: Type -> Q Exp -> Q Exp
wrapFun t e = lamE (map return (zipWith typeToPatternB ws args))
                (wrapValue r (appsE (e : (map return $ concat $ zipWith flatApp ws args))))
  where ws = map (("wa"++) . show) [0..]
        (args, r) = argsAndResult t

argsAndResult :: Type -> ([Type],Type)
argsAndResult (TFun t1 t2) = (t1:args, r)
  where (args, r) = argsAndResult t2
argsAndResult t = ([], t)

wrapPrim :: TypeConst -> Q Exp -> Q Exp
wrapPrim TInt    e = [| I# $e |]
wrapPrim TInt64  e = [| I# $e |]
wrapPrim TWord   e = [| W# $e |]
wrapPrim TWord64 e = [| W# $e |]
wrapPrim TDouble e = [| D# $e |]
wrapPrim TFloat  e = [| F# $e |]
wrapPrim tc      e = e

translateTypeConst TInt = ConT ''Int
translateTypeConst TInt64 = ConT ''Int
translateTypeConst TWord = ConT ''Word 
translateTypeConst TWord64 = ConT ''Word
translateTypeConst TFloat = ConT ''Float 
translateTypeConst TDouble =  ConT ''Double
translateTypeConst TBool = ConT ''Bool
translateTypeConst TUnit = TupleT 0


translateType :: Type -> TH.Type
translateType (TConst tc) = translateTypeConst tc
translateType (TFun  t1 t2) = (ArrowT `AppT` (translateType t1)) `AppT` (translateType t2)
translateType (TTup2 t1 t2) = ((TupleT 2) `AppT` (translateType t1)) `AppT` (translateType t2)
translateType (TTupN ts) = foldl AppT (TupleT $ length ts) (map translateType ts)
translateType (TMArr t) = (ConT ''VU.IOVector) `AppT` (translateType t)
translateType (TIArr t) = (ConT ''VU.Vector) `AppT` (translateType t)
translateType (TIO   t) = (ConT ''IO) `AppT` (translateType t)
