{-# OPTIONS_GHC -fth #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module FOASTyped where

import FOASCommon
import Types
import Eval

import Data.Array.Base
import Data.Array.IO hiding (unsafeFreeze)
import Data.Array.MArray hiding (unsafeFreeze)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.Unsafe

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

import GHC.Exts
import GHC.Real



data Expr =
  -- Int -> a
    Var Int
  -- P a -> a -> a -> a
  | BinOp BinOp Expr Expr
  -- P a -> a -> a
  | UnOp UnOp Expr
  -- Num a => Integer -> a
  | FromInteger TypeConst Integer
  -- Fractional a => Rational -> a
  | FromRational TypeConst Rational
  -- (Integral a, Num b) => a -> b
  | FromIntegral Type Expr

  -- Bool -> Bool
  | BoolLit Bool

  -- CompOp a -> a -> a -> Bool
  | Compare CompOp Expr Expr

  | Unit
  
  -- a -> b -> (a,b)
  | Tup2 Expr Expr
  -- (a,b) -> a
  | Fst Expr
  -- (a,b) -> b
  | Snd Expr

  -- [a1..an] -> (a1,..an)
  | TupN [Expr]

  -- n -> i-> (a1,..ai,..an) -> ai
  | GetN Int Int Expr
  
  -- Int -> a -> b -> b
  | Let Int Expr Expr
  
  -- (a -> b) -> a -> b
  | App Expr Expr
  -- Int -> b -> (a -> b)
  | Lambda Int Type Expr
  
  -- a -> IO a
  | Return Expr
  -- IO a -> (a -> IO b) -> IO b
  | Bind Expr Expr

  -- Bool -> a -> a -> a
  | If Expr Expr Expr
  
  -- (s -> Bool) -> (s -> s) -> s -> s
  | IterateWhile Expr Expr Expr
  -- (s -> Bool) -> (s -> s) -> (s -> IO ()) -> s -> (IO ())
  | WhileM Expr Expr Expr Expr
  
  -- (MArray IOUArray a IO, IArray UArray a) => (IO (IOUArray Int a)) -> (UArray Int a)
  | RunMutableArray Expr
  -- IArray UArray a => (UArray Int a) -> Int -> a
  | ReadIArray Expr Expr
  -- IArray UArray a => (UArray Int a) -> Int
  | ArrayLength Expr
  
  -- MArray IOUArray a IO => Int -> (IO (IOUArray Int a))
  | NewArray Type Expr
  -- MArray IOUArray a IO => (IOUArray Int a) -> Int -> (IO a)
  | ReadArray Expr Expr
  -- MArray IOUArray a IO => (IOUArray Int a) -> Int -> a -> (IO ())
  | WriteArray Expr Expr Expr
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

eq (Var v1)                (Var v2)                = v1 == v2
eq (BinOp op1 a1 b1)       (BinOp op2 a2 b2)       = op1 == op2 && a1 `eq` a2 && b1 `eq` b2
eq (Compare op1 a1 b1)     (Compare op2 a2 b2)     = op1 == op2 && a1 `eq` a2 && b1 `eq` b2
eq (UnOp op1 a1)           (UnOp op2 a2)           = op1 == op2 && a1 `eq` a2
eq (FromInteger t1 i1)     (FromInteger t2 i2)     = t1 == t2 && i1 == i2
eq (FromRational t1 r1)    (FromRational t2 r2)    = t1 == t2 && r1 == r2
eq (FromIntegral t1 a1)    (FromIntegral t2 a2)    = t1 == t2 && a1 `eq` a2
eq (BoolLit b1)            (BoolLit b2)            = b1 == b2
eq (Tup2 a1 b1)            (Tup2 a2 b2)            = a1 `eq` a2 && b1 `eq` b2
eq (Fst a1)                (Fst a2)                = a1 `eq` a2
eq (Snd a1)                (Snd a2)                = a1 `eq` a2
eq (TupN as1)              (TupN as2)              = foldl1 (&&) (zipWith eq as1 as2)
eq (GetN n1 i1 a1)         (GetN n2 i2 a2)         = n1 == n2 && i1 == i2 && a1 `eq` a2
eq (Let v1 a1 b1)          (Let v2 a2 b2)          = v1 == v2 && a1 `eq` a2 && b1 `eq` b2 
eq (App a1 b1)             (App a2 b2)             = a1 `eq` a2 && b1 `eq` b2 
eq (Lambda v1 t1 a1)       (Lambda v2 t2 a2)       = v1 == v2 && t1 == t2 && a1 `eq` a2
eq (Return a1)             (Return a2)             = a1 `eq` a2
eq (Bind a1 b1)            (Bind a2 b2)            = a1 `eq` a2 && b1 `eq` b2
eq (If a1 b1 c1)           (If a2 b2 c2)           = a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2
eq (IterateWhile a1 b1 c1) (IterateWhile a2 b2 c2) = a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2
eq (WhileM a1 b1 c1 d1)    (WhileM a2 b2 c2 d2)    = a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2 && d1 `eq` d2
eq (RunMutableArray a1)    (RunMutableArray a2)    = a1 `eq` a2
eq (ReadIArray a1 b1)      (ReadIArray a2 b2)      = a1 `eq` a2 && b1 `eq` b2
eq (ArrayLength a1)        (ArrayLength a2)        = a1 `eq` a2
eq (NewArray t1 a1)        (NewArray t2 a2)        = t1 == t2 && a1 `eq` a2
eq (ReadArray a1 b1)       (ReadArray a2 b2)       = a1 `eq` a2 && b1 `eq` b2
eq (WriteArray a1 b1 c1)   (WriteArray a2 b2 c2)   = a1 `eq` a2 && b1 `eq` b2 && c1 `eq` c2
eq (ParM a1 b1)            (ParM a2 b2)            = a1 `eq` a2 && b1 `eq` b2
eq (Unit)                  (Unit)                  = True
eq (Skip)                  (Skip)                  = True
eq (Print a1)              (Print a2)              = a1 `eq` a2
eq _                       _                       = False


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
  
cmp (Var v1)                (Var v2)                = compare v1 v2
cmp (BinOp op1 a1 b1)       (BinOp op2 a2 b2)       = compare op1 op2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (Compare op1 a1 b1)     (Compare op2 a2 b2)     = compare op1 op2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (UnOp op1 a1)           (UnOp op2 a2)           = compare op1 op2 `lexi` a1 `cmp` a2
cmp (FromInteger t1 i1)     (FromInteger t2 i2)     = compare t1 t2 `lexi` compare i1 i2
cmp (FromRational t1 r1)    (FromRational t2 r2)    = compare t1 t2 `lexi` compare r1 r2
cmp (FromIntegral t1 a1)    (FromIntegral t2 a2)    = compare t1 t2 `lexi` a1 `cmp` a2
cmp (BoolLit b1)            (BoolLit b2)            = compare b1 b2
cmp (Tup2 a1 b1)            (Tup2 a2 b2)            = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (Fst a1)                (Fst a2)                = a1 `cmp` a2
cmp (Snd a1)                (Snd a2)                = a1 `cmp` a2
cmp (TupN as1)              (TupN as2)              = cmpList as1 as2
cmp (GetN n1 i1 a1)         (GetN n2 i2 a2)         = compare n1 n2 `lexi` compare i1 i2 `lexi` a1 `cmp` a2
cmp (Let v1 a1 b1)          (Let v2 a2 b2)          = compare v1 v2 `lexi` a1 `cmp` a2 `lexi` b1 `cmp` b2 
cmp (App a1 b1)             (App a2 b2)             = a1 `cmp` a2 `lexi` b1 `cmp` b2 
cmp (Lambda v1 t1 a1)       (Lambda v2 t2 a2)       = compare v1 v2 `lexi` compare t1 t2 `lexi` a1 `cmp` a2
cmp (Return a1)             (Return a2)             = a1 `cmp` a2
cmp (Bind a1 b1)            (Bind a2 b2)            = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (If a1 b1 c1)           (If a2 b2 c2)           = a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2
cmp (IterateWhile a1 b1 c1) (IterateWhile a2 b2 c2) = a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2
cmp (WhileM a1 b1 c1 d1)    (WhileM a2 b2 c2 d2)    = a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2 `lexi` d1 `cmp` d2
cmp (RunMutableArray a1)    (RunMutableArray a2)    = a1 `cmp` a2
cmp (ReadIArray a1 b1)      (ReadIArray a2 b2)      = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (ArrayLength a1)        (ArrayLength a2)        = a1 `cmp` a2
cmp (NewArray t1 a1)        (NewArray t2 a2)        = compare t1 t2 `lexi` a1 `cmp` a2
cmp (ReadArray a1 b1)       (ReadArray a2 b2)       = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (WriteArray a1 b1 c1)   (WriteArray a2 b2 c2)   = a1 `cmp` a2 `lexi` b1 `cmp` b2 `lexi` c1 `cmp` c2
cmp (ParM a1 b1)            (ParM a2 b2)            = a1 `cmp` a2 `lexi` b1 `cmp` b2
cmp (Skip)                  (Skip)                  = EQ
cmp (Print a1)              (Print a2)              = a1 `cmp` a2
cmp e1 e2                                           = compare (exprOrd e1) (exprOrd e2)

exprOrd :: Expr -> Int
exprOrd (Var _)              = 1
exprOrd (BinOp _ _ _)        = 2
exprOrd (Compare _ _ _)      = 3
exprOrd (UnOp _ _)           = 4
exprOrd (FromInteger _ _)    = 5
exprOrd (FromRational _ _)   = 6
exprOrd (FromIntegral _ _)   = 7
exprOrd (BoolLit _)          = 8
exprOrd (Tup2 _ _)           = 9
exprOrd (Fst _)              = 10
exprOrd (Snd _)              = 11
exprOrd (TupN _)             = 12
exprOrd (GetN _ _ _)         = 13
exprOrd (Let _ _ _)          = 14
exprOrd (App _ _)            = 15
exprOrd (Lambda _ _ _)       = 16
exprOrd (Return _)           = 17
exprOrd (Bind _ _)           = 18
exprOrd (If _ _ _)           = 19
exprOrd (IterateWhile _ _ _) = 20
exprOrd (WhileM _ _ _ _)     = 21
exprOrd (RunMutableArray _)  = 22
exprOrd (ReadIArray _ _)     = 23
exprOrd (ArrayLength _)      = 24
exprOrd (NewArray _ _)       = 25
exprOrd (ReadArray _ _)      = 26
exprOrd (WriteArray _ _ _)   = 28
exprOrd (ParM _ _)           = 29
exprOrd (Unit)               = 30
exprOrd (Skip)               = 31
exprOrd (Print _)            = 32

-- General traversal

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
exprTrav f g e@(FromIntegral t e1) = liftM ((FromIntegral t) *** id) (exprTraverse f g e1)
exprTrav f g e@(UnOp op e1) = liftM ((UnOp op) *** id) (exprTraverse f g e1)
exprTrav f g e@(Fst e1) = liftM (Fst *** id) (exprTraverse f g e1)
exprTrav f g e@(Snd e1) = liftM (Snd *** id) (exprTraverse f g e1)
exprTrav f g e@(Lambda v t e1) = liftM ((Lambda v t) *** id) (exprTraverse f g e1)
exprTrav f g e@(Return e1) = liftM (Return *** id) (exprTraverse f g e1)
exprTrav f g e@(NewArray t e1) = liftM ((NewArray t) *** id) (exprTraverse f g e1)
exprTrav f g e@(RunMutableArray e1) = liftM (RunMutableArray *** id) (exprTraverse f g e1)
exprTrav f g e@(ArrayLength e1) = liftM (ArrayLength *** id) (exprTraverse f g e1)
exprTrav f g e@(Print e1) = liftM (Print *** id) (exprTraverse f g e1)
exprTrav f g e@(GetN l n e1) = liftM ((GetN l n) *** id) (exprTraverse f g e1)

exprTrav f g e@(App e1 e2) = liftM2 (App **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(BinOp op e1 e2) = liftM2 ((BinOp op) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Compare op e1 e2) = liftM2 ((Compare op) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Tup2 e1 e2) = liftM2 (Tup2 **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Let v e1 e2) = liftM2 ((Let v) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Bind e1 e2) = liftM2 (Bind **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ReadIArray e1 e2) = liftM2 (ReadIArray **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ReadArray e1 e2) = liftM2 (ReadArray **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ParM e1 e2) = liftM2 (ParM **** g) (exprTraverse f g e1) (exprTraverse f g e2)

exprTrav f g e@(If e1 e2 e3) = liftM3 (If ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)
exprTrav f g e@(IterateWhile e1 e2 e3) = liftM3 (IterateWhile ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)
exprTrav f g e@(WriteArray e1 e2 e3) = liftM3 (WriteArray ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)

exprTrav f g e@(WhileM e1 e2 e3 e4) = liftM4 (WhileM ****** (reducel4 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3) (exprTraverse f g e4)
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
         Just (b,c) | b /= 0x3fffffff && c <= 1 && b == b' || not (worthIt 1 e1') ->
           do e2' <- local (first $ IM.insert v e1') $ undoSome' map k e2
              return e2'
         _ -> 
           do e2' <- undoSome' map k e2
              return (Let v e1' e2')
undoSome' map k e | isAtomic e = return e
                  | otherwise  = k e

worthIt :: Int -> Expr -> Bool
worthIt i e | isAtomic e = False
worthIt 0 e              = True
worthIt i (Tup2 e1 e2)       = worthIt (i-1) e1 || worthIt (i-1) e2
worthIt i (BinOp op e1 e2)   = worthIt (i-1) e1 || worthIt (i-1) e2
worthIt i (Compare op e1 e2) = worthIt (i-1) e1 || worthIt (i-1) e2
worthIt i (UnOp op e)        = worthIt (i-1) e
worthIt i (FromIntegral t e) = worthIt (i-1) e
worthIt i (Fst e)            = worthIt (i-1) e
worthIt i (Snd e)            = worthIt (i-1) e
worthIt i (Return e)         = worthIt (i-1) e
worthIt i (NewArray t e)     = worthIt i e
worthIt i e = True


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
        eFinal = trace ("e'': " ++ (show e'')) $ undoSome varMap' e''

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
showExpr d (UnOp op a) =
  case op of
    Abs    -> showApp d "abs" [a]
    Signum -> showApp d "signum" [a]
    Recip  -> showApp d "recip" [a]
showExpr d (BinOp op a b)  = showBinOp d op a b
showExpr d (Compare op a b) = showCompOp d op a b
showExpr d (FromInteger t n) = showParen (d > 0) $ shows n . showString " :: " . shows t
showExpr d (FromRational t r) =
  case t of
    TFloat  -> shows (fromRational r :: Float)
    TDouble -> shows (fromRational r :: Double)
showExpr d (FromIntegral t a) = showApp d "fromIntegral" [a]
showExpr d (BoolLit b)     = shows b
showExpr d (Unit) = showString "()"
showExpr d (Tup2 a b)    = showParen True $ showsPrec 0 a . showString ", " . showsPrec 0 b
showExpr d (Fst a) = showApp d "fst" [a]
showExpr d (Snd a) = showApp d "snd" [a]
showExpr d (TupN as) = showString "(" . showsTup as
showExpr d (GetN l n a) = showApp d ("get" ++ (show l) ++ "_" ++ (show n)) [a]
showExpr d (Return a) = showApp d "return" [a]
showExpr d (Bind m f) = showParen (d > 1) $ showsPrec 1 m . showString " >>= " . showsPrec 2 f
showExpr d (If cond a b) = showParen (d > 0) $ showString "if " . showsPrec 0 cond . showString " then " . showsPrec 0 a . showString " else " . showsPrec 0 b
showExpr d (IterateWhile cond step init) = showApp d "iterateWhile" [cond,step,init]
showExpr d (WhileM cond step action init) = showApp d "whileM" [cond,step,action,init]
showExpr d (RunMutableArray arr) = showApp d "runMutableArray" [arr]
showExpr d (ReadIArray arr ix)   = showApp d "readIArray" [arr,ix]
showExpr d (ArrayLength arr)     = showApp d "arrayLength" [arr]
showExpr d (NewArray t l)        = showApp d "newArray" [l]
showExpr d (ReadArray arr ix)    = showApp d "readArray" [arr,ix]
showExpr d (WriteArray arr ix a) = showApp d "writeArray" [arr,ix,a]
showExpr d (ParM n f) = showApp d "parM" [n,f]
showExpr d Skip = showString "skip"
showExpr d (Print a) = showApp d "print" [a]
showExpr d (Let v e1 e2) = showParen (d > 10) $ showString "let " . showsVar v . showString " = " . showsPrec 0 e1 . showString " in " . showsPrec 0 e2
showExpr d (Lambda v t e) = showString "(\\" . showsVar v . showString " :: " . shows t . showString " -> " . showsPrec 0 e . showString ")"
showExpr d (App e1 e2) = showApp d (showsPrec 10 e1 "") [e2]

showsTup (a:[]) = showsPrec 0 a . showString ")"
showsTup (a:as) = showsPrec 0 a . showString "," . showsTup as

showApp :: Int -> String -> [Expr] -> ShowS
showApp d f es = showParen (d > 10) $ showString f . foldr1 (.) (map ((showString " " .) . showsPrec 11) es)

showsVar :: Int -> ShowS
showsVar v | v < 0x40000000 = showString "x" . shows v
           | otherwise      = showString "y" . shows (v - 0x40000000)

showVar v = showsVar v ""


-- Translation

translate :: Expr -> Q Exp
translate (Var v) = dyn (showVar v)
translate (UnOp op e) = translateUnOp op (translate e)
translate (BinOp op e1 e2) = translateBinOp op (translate e1) (translate e2)
translate (FromInteger t i) = translateFromInteger t i
translate (FromRational t (a :% b)) = sigE [| fromRational (a :% b) |] (translateTypeConst t)
translate (FromIntegral t e) = sigE [| fromIntegral $(translate e) |] (translateType t)
translate (BoolLit b) = [| b |]
translate (Compare op e1 e2) = translateCompOp op (translate e1) (translate e2)
translate (Unit) = [| () |]
translate (Tup2 e1 e2) = tupE [translate e1, translate e2]
translate (Fst e) = [| fst $(translate e) |]
translate (Snd e) = [| snd $(translate e) |]
translate (TupN es) = tupE (map translate es)
translate (GetN n i e) =
  do x <- newName "get"
     let pat = tupP $ (replicate i wildP) ++ [varP x] ++ (replicate (n-i-1) wildP)
     caseE (translate e) [match pat (normalB (varE x)) []]
translate (App e1 e2) = [| let a = $(translate e2) in a `maybeDeepSeq` $(translate e1) a |]
translate (Let v e1 e2) = letE [valD (varP v') (normalB (translate e1)) []] [| $(varE v') `maybeDeepSeq` $(translate e2) |]
  where v' = mkName (showVar v)
translate (Lambda v _ e1) = lam1E (varP v') [| $(varE v') `maybeDeepSeq` $(translate e1) |]
  where v' = mkName (showVar v)
translate (Return e) = [| return $(translate e) |]
translate (Bind e1 e2) = [| $(translate e1) >>= $(translate e2) |]
translate (If e1 e2 e3) = [| if $(translate e1) then $(translate e2) else $(translate e3) |]
translate (IterateWhile e1 e2 e3) =
  [| while $(translate e1) $(translate e2) $(translate e3) |]
translate (WhileM e1 e2 e3 e4) =
  [| whileM $(translate e1) $(translate e2) $(translate e3) $(translate e4) |]
translate (RunMutableArray e) = [| runMutableArray $(translate e) |]
translate (ReadIArray e1 e2) = [| $(translate e1) `unsafeAt` $(translate e2) |]
translate (ArrayLength e) = [| snd (bounds $(translate e)) + 1 |]
translate (NewArray t e) = sigE [| newIOUArray (0,$(translate e)-1) |] (translateType (TIO $ TMArr t))
translate (WriteArray e1 e2 e3) = [| unsafeWrite $(translate e1) $(translate e2) $(translate e3) |]
translate (ReadArray e1 e2) = [| unsafeRead $(translate e1) $(translate e2) |]
translate (ParM e1 e2) = [| parM $(translate e1) $(translate e2) |]
translate Skip = [| return () |]
translate (Print e) = [| print $(translate e) |]


translateFromInteger :: TypeConst -> Integer -> Q Exp
translateFromInteger TInt i = sigE [| i |] [t| Int |]
translateFromInteger TInt64 i = sigE [| i |] [t| Int64 |]
translateFromInteger TWord i = sigE [| i |] [t| Word |]
translateFromInteger TWord64 i = sigE [| i |] [t| Word64 |]
translateFromInteger TFloat i = sigE [| i |] [t| Float |]
translateFromInteger TDouble i = sigE [| i |] [t| Double |]

translateUnOp :: UnOp -> Q Exp -> Q Exp
translateUnOp Abs    q = [| abs $(q) |]
translateUnOp Signum q = [| signum $(q) |]
translateUnOp Recip  q = [| recip $(q) |]
      
translateBinOp :: BinOp -> Q Exp -> Q Exp -> Q Exp
translateBinOp Minus q1 q2 = [| $(q1) - $(q2) |]
translateBinOp Plus  q1 q2 = [| $(q1) + $(q2) |]
translateBinOp Mult  q1 q2 = [| $(q1) * $(q2) |]
translateBinOp Quot  q1 q2 = [| $(q1) `quot` $(q2) |]
translateBinOp Rem   q1 q2 = [| $(q1) `rem` $(q2) |]
translateBinOp Div   q1 q2 = [| $(q1) `div` $(q2) |]
translateBinOp Mod   q1 q2 = [| $(q1) `mod` $(q2) |]
translateBinOp FDiv  q1 q2 = [| $(q1) / $(q2) |]
translateBinOp Min   q1 q2 = [| min $(q1) $(q2) |]
translateBinOp Max   q1 q2 = [| max $(q1) $(q2) |]
translateBinOp And   q1 q2 = [| $(q1) && $(q2) |]
translateBinOp Or    q1 q2 = [| $(q1) || $(q2) |]

translateCompOp :: CompOp -> Q Exp -> Q Exp -> Q Exp
translateCompOp EQU q1 q2 = [| $(q1) == $(q2) |]
translateCompOp NEQ q1 q2 = [| $(q1) /= $(q2) |]
translateCompOp GTH q1 q2 = [| $(q1) >  $(q2) |]
translateCompOp LTH q1 q2 = [| $(q1) <  $(q2) |]
translateCompOp GEQ q1 q2 = [| $(q1) >= $(q2) |]
translateCompOp LEQ q1 q2 = [| $(q1) <= $(q2) |]

translateTypeConst :: TypeConst -> Q TH.Type
translateTypeConst TInt = [t| Int |]
translateTypeConst TInt64 = [t| Int64 |]
translateTypeConst TWord = [t| Word |]
translateTypeConst TWord64 = [t| Word64 |]
translateTypeConst TFloat = [t| Float |]
translateTypeConst TDouble =  [t| Double |]
translateTypeConst TBool = [t| Bool |]
translateTypeConst TUnit = [t| () |]

translateType :: Type -> Q TH.Type
translateType (TConst tc) = translateTypeConst tc
translateType (TFun  t1 t2) = [t| $(translateType t1) -> $(translateType t2) |]
translateType (TTup2 t1 t2) = [t| ($(translateType t1), $(translateType t2)) |]
translateType (TTupN ts) = foldl appT (tupleT $ length ts) (map translateType ts)
translateType (TMArr t) = [t| IOUArray Int $(translateType t) |]
translateType (TIArr t) = [t| UArray Int $(translateType t) |]
translateType (TIO   t) = [t| IO $(translateType t) |]
