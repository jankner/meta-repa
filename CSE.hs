module CSE (cse) where

import FOASTyped
import TypeCheck
import Types

-- CSE

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


thing :: (Expr -> CSEM (Expr,IS.IntSet)) -> Expr -> CSEM (Expr,IS.IntSet)
thing f (Var v) = return (Var v, IS.singleton v)
thing f (Let v e1 t1 e2) = do
  (e2',vs2) <- f e2
  st <- get
  let (exprs,newMap) = extractExprsLE (exprMap st) v
  let e2Final = replaceExprs v exprs e2'
  put (st {exprMap = newMap})
  (e1',vs1) <- f e1
  v1 <- addExpr e1' vs1
  return (Let v (Var v1) t1 e2Final, IS.difference (IS.union vs1 vs2) (IS.singleton v))
thing f (Lambda v t e) = do
  (e',vs) <- f e
  st <- get
  let (exprs,newMap) = extractExprsLE (exprMap st) v
  let eFinal = replaceExprs v exprs e'
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
letBind e (_,e',v,_) = Let v e' t e
  where t = case runTC2 (inferT2 e') of
              Right t  -> t
              Left err -> error err

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

