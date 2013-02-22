module FOAS where


import Data.List
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Maybe

import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

data Expr =
  -- Int -> a
    Var Int
  -- P a -> a -> a -> a
  | BinOp BinOp Expr Expr
  -- Num a => a -> a
  | Abs Expr
  -- Num a => a -> a
  | Signum Expr
  -- Num a => Integer -> Int ?
  | FromInteger Integer

  -- Bool -> Bool
  | BoolLit Bool

  -- CompOp a -> a -> a -> Bool
  | Compare CompOp Expr Expr
  
  -- a -> b -> (a,b)
  | Tup2 Expr Expr
  -- (a,b) -> a
  | Fst Expr
  -- (a,b) -> b
  | Snd Expr
  
  -- Int -> a -> b -> b
  | Let Int Expr Expr
  
  -- Int -> b -> (a -> b)
  | Lambda Int Expr
  
  -- a -> IO a
  | Return Expr
  -- IO a -> (a -> IO b) -> IO b
  | Bind Expr Expr
  
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
  | NewArray Expr
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
    deriving (Eq, Ord)

data BinOp = Plus  -- Num a => P a
           | Minus -- Num a => P a
           | Mult  -- Num a => P a
           | Quot -- Integral a => P a
           | Rem  -- Integral a => P a
           | Min -- Ord a => P a
           | Max -- Ord a => P a
           | And -- P Bool
           | Or  -- P Bool
  deriving (Show, Eq, Ord)

data CompOp = EQU  -- Eq a => CompOp a
            | NEQ -- Eq a => CompOp a
            | GTH -- Ord a => CompOp a
            | LTH -- Ord a => CompOp a
            | GEQ -- Ord a => CompOp a
            | LEQ -- Ord a => CompOp a
  deriving (Show, Eq, Ord)


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
exprRec f g2 g3 g4 e@(Abs e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Fst e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Snd e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Signum e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Return e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(NewArray e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(RunMutableArray e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(ArrayLength e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Print e1) = exprFold f g2 g3 g4 e1

exprRec f g2 g3 g4 e@(BinOp op e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Compare op e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Tup2 e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Let v e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Bind e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ReadIArray e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ReadArray e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ParM e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)

exprRec f g2 g3 g4 e@(IterateWhile e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)
exprRec f g2 g3 g4 e@(WriteArray e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)

exprRec f g2 g3 g4 e@(WhileM e1 e2 e3 e4) = g4 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3) (exprFold f g2 g3 g4 e4)


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
exprTrav f g e@(Abs e1) = liftM (Abs *** id) (exprTraverse f g e1)
exprTrav f g e@(Fst e1) = liftM (Fst *** id) (exprTraverse f g e1)
exprTrav f g e@(Snd e1) = liftM (Snd *** id) (exprTraverse f g e1)
exprTrav f g e@(Lambda v e1) = liftM ((Lambda v) *** id) (exprTraverse f g e1)
exprTrav f g e@(Signum e1) = liftM (Signum *** id) (exprTraverse f g e1)
exprTrav f g e@(Return e1) = liftM (Return *** id) (exprTraverse f g e1)
exprTrav f g e@(NewArray e1) = liftM (NewArray *** id) (exprTraverse f g e1)
exprTrav f g e@(RunMutableArray e1) = liftM (RunMutableArray *** id) (exprTraverse f g e1)
exprTrav f g e@(ArrayLength e1) = liftM (ArrayLength *** id) (exprTraverse f g e1)
exprTrav f g e@(Print e1) = liftM (Print *** id) (exprTraverse f g e1)

exprTrav f g e@(BinOp op e1 e2) = liftM2 ((BinOp op) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Compare op e1 e2) = liftM2 ((Compare op) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Tup2 e1 e2) = liftM2 (Tup2 **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Let v e1 e2) = liftM2 ((Let v) **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(Bind e1 e2) = liftM2 (Bind **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ReadIArray e1 e2) = liftM2 (ReadIArray **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ReadArray e1 e2) = liftM2 (ReadArray **** g) (exprTraverse f g e1) (exprTraverse f g e2)
exprTrav f g e@(ParM e1 e2) = liftM2 (ParM **** g) (exprTraverse f g e1) (exprTraverse f g e2)

exprTrav f g e@(IterateWhile e1 e2 e3) = liftM3 (IterateWhile ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)
exprTrav f g e@(WriteArray e1 e2 e3) = liftM3 (WriteArray ***** (reducel3 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3)

exprTrav f g e@(WhileM e1 e2 e3 e4) = liftM4 (WhileM ****** (reducel4 g)) (exprTraverse f g e1) (exprTraverse f g e2) (exprTraverse f g e3) (exprTraverse f g e4)
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
isAtomic (Var _)         = True
isAtomic (FromInteger _) = True
isAtomic (BoolLit _)     = True
isAtomic (Skip)          = True
isAtomic _ = False

findMin :: IS.IntSet -> Maybe Int
findMin s | IS.null s = Nothing
          | otherwise  = Just (IS.findMin s)

minVar :: IS.IntSet -> Int
minVar = (fromMaybe 0x3fffffff) .  findMin 


data CSEState = CSEState { exprMap :: IM.IntMap (M.Map Expr (Int, Int)), varCounter :: Int }

type CSEM a = State CSEState a

cse :: Expr -> Expr
cse e = evalState (stuff e) (CSEState {exprMap = IM.empty, varCounter = 0x40000000})
  where stuff e = 
          do (e',vs) <- exprTraverse thing IS.union e
             st <- get
             let exprs = exprSort $ exprMapToList (exprMap st)
             let eFinal = foldl letBind e' exprs
             return eFinal
        exprSort = sortBy $ \(_,_,v1,_) (_,_,v2,_) -> compare v2 v1

--showStuff :: (Int,Expr,Int,Int) -> String
--showStuff (l,e,v,c) = "v: " ++ (showVar v)--"!(" ++ (show l) ++ ", " ++ (showVar v) ++ ", " ++ (show c) ++ ", " ++ (show e) ++ ")"


thing :: (Expr -> CSEM (Expr,IS.IntSet)) -> Expr -> CSEM (Expr,IS.IntSet)
thing f (Var v) = return (Var v, IS.singleton v)
thing f (Let v e1 e2) = do
  (e2',vs2) <- f e2
  st <- get
  let (exprs,newMap) = extractExprsLE (exprMap st) v
  let e2Final = replaceExprs v exprs e2' -- trace ("exprs " ++ (show v) ++ ": " ++ (show exprs)) $ 
  put (st {exprMap = newMap})
  (e1',vs1) <- f e1
  v1 <- addExpr e1' vs1
  return (Let v (Var v1) e2Final, IS.difference (IS.union vs1 vs2) (IS.singleton v))
thing f (Lambda v e) = do
  (e',vs) <- f e
  st <- get
  let (exprs,newMap) = extractExprsLE (exprMap st) v
  let eFinal = replaceExprs v exprs e' -- trace ("exprs " ++ (show v) ++ ": " ++ (show exprs)) $ 
  put (st {exprMap = newMap})
  return (Lambda v eFinal, IS.difference vs (IS.singleton v))
thing f e | isAtomic e = return (e, IS.empty)
thing f e | otherwise  = do
  (e',vs) <- f e
  v <- addExpr e' vs
  return (Var v, vs)


exprMapToList :: IM.IntMap (M.Map Expr (Int,Int)) -> [(Int,Expr,Int,Int)]
exprMapToList exprMap = concatMap (uncurry mapToList) $ IM.toAscList exprMap

extractExprsLE :: IM.IntMap (M.Map Expr (Int,Int)) -> Int -> ([(Int,Expr,Int,Int)], IM.IntMap (M.Map Expr (Int,Int)))
extractExprsLE exprMap v = (exprs,newMap)
  where exprs = (concatMap (mapToList v) $ maybeToList x) ++ (concatMap (uncurry mapToList) $ IM.toAscList restMap) 
        (restMap, x, newMap) = IM.splitLookup v exprMap

mapToList :: Int -> M.Map Expr (Int,Int) -> [(Int,Expr,Int,Int)]
mapToList i m = zipWith tupCons3 (repeat i) (map (uncurry tupCons2) (M.toList m))
  where tupCons2 a (b,c) = (a,b,c)
        tupCons3 a (b,c,d) = (a,b,c,d)

replaceExprs :: Int -> [(Int,Expr,Int,Int)] -> Expr -> Expr
replaceExprs v es e = foldl letBind (substituteExprs subExprs e) letExprs'
  where (letExprs, subExprs) = partition p es
        letExprs' = sortBy (\(_,_,v1,_) (_,_,v2,_) -> compare v2 v1) letExprs
        p (b,e,v',c) =  b < v || c > 1

letBind :: Expr -> (Int,Expr,Int,Int) -> Expr
letBind e (_,e',v,_) = Let v e' e

substituteExprs :: [(Int,Expr,Int,Int)] -> Expr -> Expr
substituteExprs xs e = subVar exprMap e
  where exprMap = IM.fromList $ map f xs
        f (_,e,v,_) = (v, subVar exprMap e)

subVar :: IM.IntMap Expr -> Expr -> Expr
subVar m e = fst $ runReader (exprTraverse subV (\a b -> ()) e) m

subV :: (Expr -> Reader (IM.IntMap Expr) (Expr,())) -> Expr -> Reader (IM.IntMap Expr) (Expr,()) 
subV f (Var v) = do
  me <- reader (IM.lookup v)
  case me of
    Just e  -> return (e,())
    Nothing -> return (Var v,())
subV f e | isAtomic e = return (e,())
         | otherwise  = f e


removeWithDefault :: Int -> a -> IM.IntMap a -> (a, IM.IntMap a)
removeWithDefault k a map = (fromMaybe a old, map')
  where (old, map') = IM.updateLookupWithKey (\_ _ -> Nothing) k map
 
addExpr :: Expr -> IS.IntSet -> CSEM Int
addExpr e vs = do
  st <- get
  let l = minVar vs
  let map = exprMap st
  let subMap = IM.findWithDefault M.empty l map
  let (x,newSubMap) = M.insertLookupWithKey (\key _ (oldv,oldc) -> (oldv,oldc+1)) e (varCounter st, 1) subMap
  case x of
    Just (v,_) -> do
      put (st {exprMap = IM.insert l newSubMap map})
      return v --trace ("l: " ++ (show l) ++ ", v: " ++ (showVar v) ++ ", c: " ++ (show $ snd (fromJust $ M.lookup e newSubMap)) ++ ", e: " ++ (show e)) $ 
    Nothing  -> do
      let v = varCounter st
      put (st {exprMap = IM.insert l newSubMap map, varCounter = v + 1})
      return v --trace ("l: " ++ (show l) ++ ", v: " ++ (showVar v) ++ ", e: " ++ (show e)) $ 


instance Show Expr where
  showsPrec = showExpr

showExpr :: Int -> Expr -> ShowS
showExpr d (Var v) = showsVar v
showExpr d (BinOp op a b)  = showBinOp d op a b
showExpr d (Compare op a b) = showCompOp d op a b
showExpr d (Abs a)         = showApp d "abs" [a]
showExpr d (Signum a)      = showApp d "signum" [a]
showExpr d (FromInteger n) = shows n
showExpr d (BoolLit b)     = shows b
showExpr d (Tup2 a b)    = showParen True $ showsPrec 0 a . showString ", " . showsPrec 0 b
showExpr d (Fst a) = showApp d "fst" [a]
showExpr d (Snd a) = showApp d "fst" [a]
showExpr d (Return a) = showApp d "return" [a]
showExpr d (Bind m f) = showParen (d > 1) $ showsPrec 1 m . showString " >>= " . showsPrec 2 f
showExpr d (IterateWhile cond step init) = showApp d "iterateWhile" [cond,step,init]
showExpr d (WhileM cond step action init) = showApp d "whileM" [cond,step,action,init]
showExpr d (RunMutableArray arr) = showApp d "runMutableArray" [arr]
showExpr d (ReadIArray arr ix)   = showApp d "readIArray" [arr,ix]
showExpr d (ArrayLength arr)     = showApp d "arrayLength" [arr]
showExpr d (NewArray l)          = showApp d "newArray" [l]
showExpr d (ReadArray arr ix)    = showApp d "readArray" [arr,ix]
showExpr d (WriteArray arr ix a) = showApp d "writeArray" [arr,ix,a]
showExpr d (ParM n f) = showApp d "parM" [n,f]
showExpr d Skip = showString "skip"
showExpr d (Print a) = showApp d "print" [a]
showExpr d (Let v e1 e2) = showParen (d > 10) $ showString "let " . showsVar v . showString " = " . showsPrec 0 e1 . showString " in " . showsPrec 0 e2
showExpr d (Lambda v e) = showParen (d > 10) $ showString "\\" . showsVar v . showString " -> " . showsPrec 0 e

showApp :: Int -> String -> [Expr] -> ShowS
showApp d f es = showParen (d > 10) $ showString f . foldr1 (.) (map ((showString " " .) . showsPrec 11) es)

showsVar :: Int -> ShowS
showsVar v | v < 0x40000000 = showString "x" . shows v
           | otherwise      = showString "y" . shows (v - 0x40000000)

showVar v = showsVar v ""

showBinOp :: Int -> BinOp -> Expr -> Expr -> ShowS
showBinOp d Minus a b = showParen (d > 6) $ showsPrec 6 a . showString " - " . showsPrec 7 b
showBinOp d Plus  a b = showParen (d > 6) $ showsPrec 6 a . showString " + " . showsPrec 7 b
showBinOp d Mult  a b = showParen (d > 7) $ showsPrec 7 a . showString " * " . showsPrec 8 b
showBinOp d Quot  a b = showParen (d > 7) $ showsPrec 7 a . showString " `quot` " . showsPrec 8 b
showBinOp d Rem   a b = showParen (d > 7) $ showsPrec 7 a . showString " `rem` " . showsPrec 8 b
showBinOp d Min   a b = showParen (d > 10) $ showString "min " . showsPrec 10 a . showsPrec 10 b
showBinOp d Max   a b = showParen (d > 10) $ showString "max " . showsPrec 10 a . showsPrec 10 b
showBinOp d And   a b = showParen (d > 3) $ showsPrec 3 a . showString " && " . showsPrec 4 b
showBinOp d Or    a b = showParen (d > 2) $ showsPrec 2 a . showString " || " . showsPrec 3 b



showCompOp :: Int -> CompOp -> Expr -> Expr -> ShowS
showCompOp d EQU  a b = showParen (d > 4) $ showsPrec 4 a . showString " == " . showsPrec 4 b
showCompOp d NEQ a b = showParen (d > 4) $ showsPrec 4 a . showString " /= " . showsPrec 4 b
showCompOp d GTH a b = showParen (d > 4) $ showsPrec 4 a . showString " > " . showsPrec 4 b
showCompOp d LTH a b = showParen (d > 4) $ showsPrec 4 a . showString " < " . showsPrec 4 b
showCompOp d GEQ a b = showParen (d > 4) $ showsPrec 4 a . showString " >= " . showsPrec 4 b
showCompOp d LEQ a b = showParen (d > 4) $ showsPrec 4 a . showString " <= " . showsPrec 4 b

