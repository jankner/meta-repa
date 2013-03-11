module FOAS where

import FOASCommon
import Types

import Data.List
import qualified Data.Map as M
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Maybe

import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Identity

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
  
  -- a -> b -> (a,b)
  | Tup2 Expr Expr
  -- (a,b) -> a
  | Fst Expr
  -- (a,b) -> b
  | Snd Expr

  -- [a1..an] -> (a1,..an)
  | TupN [Expr]

  -- n -> m -> (a1,..am,..an) -> am
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


fixTuples :: Expr -> Expr
fixTuples = runIdentity . (exprTraverse0 f)
  where
    f k (Tup2 e1 e2) =
      case (e1,e2) of
        (Fst e1', Snd e2') | e1' == e2' -> f k e1'
        _ -> do e1' <- f k e1
                e2' <- f k e2
                return (Tup2 e1' e2')
    f k (TupN es) =
      case tupleCheck es of
        Just e' -> f k e'
        Nothing -> liftM TupN $ mapM (f k) es
    f k e | isAtomic e = return e
          | otherwise  = k e

data D = D Expr Int 

tupleCheck :: [Expr] -> Maybe Expr 
tupleCheck (GetN n i e : es) = tupleCheck' 1 e es
  where
    tupleCheck' i e [] = Just e
    tupleCheck' i e ((GetN n i' e'):es)
      | i == i' && e == e' = tupleCheck' (i+1) e es
    tupleCheck' i e (_:es) = Nothing
tupleCheck (e          : es) = Nothing

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
exprRec f g2 g3 g4 e@(FromIntegral t e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(UnOp op e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Fst e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Snd e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Return e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(NewArray e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(RunMutableArray e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(ArrayLength e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Print e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(GetN l n e1) = exprFold f g2 g3 g4 e1
exprRec f g2 g3 g4 e@(Lambda v t e1) = exprFold f g2 g3 g4 e1

exprRec f g2 g3 g4 e@(App e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(BinOp op e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Compare op e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Tup2 e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Let v e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(Bind e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ReadIArray e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ReadArray e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)
exprRec f g2 g3 g4 e@(ParM e1 e2) = g2 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2)

exprRec f g2 g3 g4 e@(If e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)
exprRec f g2 g3 g4 e@(IterateWhile e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)
exprRec f g2 g3 g4 e@(WriteArray e1 e2 e3) = g3 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3)

exprRec f g2 g3 g4 e@(WhileM e1 e2 e3 e4) = g4 (exprFold f g2 g3 g4 e1) (exprFold f g2 g3 g4 e2) (exprFold f g2 g3 g4 e3) (exprFold f g2 g3 g4 e4)

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
exprTrav f g e@(FromIntegral t e1) = liftM ((FromIntegral t) *** id) (exprTraverse f g e1)
exprTrav f g e@(UnOp op e1) = liftM ((UnOp op) *** id) (exprTraverse f g e1)
exprTrav f g e@(Fst e1) = liftM (Fst *** id) (exprTraverse f g e1)
exprTrav f g e@(Snd e1) = liftM (Snd *** id) (exprTraverse f g e1)
exprTrav f g e@(Lambda v t e1) = liftM ((Lambda v t) *** id) (exprTraverse f g e1)
exprTrav f g e@(Return e1) = liftM (Return *** id) (exprTraverse f g e1)
exprTrav f g e@(NewArray e1) = liftM (NewArray *** id) (exprTraverse f g e1)
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
thing f (Lambda v t e) = do
  (e',vs) <- f e
  st <- get
  let (exprs,newMap) = extractExprsLE (exprMap st) v
  let eFinal = replaceExprs v exprs e' -- trace ("exprs " ++ (show v) ++ ": " ++ (show exprs)) $ 
  put (st {exprMap = newMap})
  return (Lambda v t eFinal, IS.difference vs (IS.singleton v))
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
      return v
    Nothing  -> do
      let v = varCounter st
      put (st {exprMap = IM.insert l newSubMap map, varCounter = v + 1})
      return v


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
showExpr d (FromInteger t i) = shows i
showExpr d (FromRational t r) =
  case t of
    TFloat  -> shows (fromRational r :: Float)
    TDouble -> shows (fromRational r :: Double)
showExpr d (FromIntegral t a) = showApp d "fromIntegral" [a]
showExpr d (BoolLit b) = shows b
showExpr d (Tup2 a b) = showParen True $ showsPrec 0 a . showString ", " . showsPrec 0 b
showExpr d (Fst a) = showApp d "fst" [a]
showExpr d (Snd a) = showApp d "fst" [a]
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
showExpr d (NewArray l)          = showApp d "newArray" [l]
showExpr d (ReadArray arr ix)    = showApp d "readArray" [arr,ix]
showExpr d (WriteArray arr ix a) = showApp d "writeArray" [arr,ix,a]
showExpr d (ParM n f) = showApp d "parM" [n,f]
showExpr d Skip = showString "skip"
showExpr d (Print a) = showApp d "print" [a]
showExpr d (Let v e1 e2) = showParen (d > 10) $ showString "let " . showsVar v . showString " = " . showsPrec 0 e1 . showString " in " . showsPrec 0 e2
showExpr d (Lambda v t e) = showString "(\\" . showsVar v . showString " -> " . showsPrec 0 e . showString ")"
showExpr d (App e1 e2) = showApp d (showsPrec 10 e1 "") [e2]

showsTup (a:[]) = showsPrec 0 a . showString ")"
showsTup (a:as) = showsPrec 0 a . showString "," . showsTup as

showApp :: Int -> String -> [Expr] -> ShowS
showApp d f es = showParen (d > 10) $ showString f . foldr1 (.) (map ((showString " " .) . showsPrec 11) es)

showsVar :: Int -> ShowS
showsVar v | v < 0x40000000 = showString "x" . shows v
           | otherwise      = showString "y" . shows (v - 0x40000000)

showVar v = showsVar v ""

