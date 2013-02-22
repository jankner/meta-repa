{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE Rank2Types #-}
module TypeCheck where

import FOAS
import Types

import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.ST

import Control.Arrow


data TCState = TCState { typeVarCounter :: TypeVar, sortContext :: SortContext}
  deriving Show

newtype TC a = TC {unTC :: ErrorT String (StateT TCState (ReaderT Env IO)) a}
  deriving (Monad,MonadIO,MonadState TCState,MonadReader Env,MonadError String)


runTC tc = liftM fst $ runReaderT (runStateT (runErrorT (unTC tc)) startState) []
  where startState = TCState {typeVarCounter = 0, sortContext = M.empty}

lookupVar :: (MonadError String m, MonadReader Env m) => Int -> m Type
lookupVar v = do
  mt <- reader (lookup v)
  case mt of
    Just t -> return t
    Nothing -> throwError ("unknown variable: " ++ (showVar v))

addVar :: MonadReader Env m => Int -> Type -> m a -> m a
addVar v t m = local ((v,t):) m

envSubst :: MonadReader Env m => Subst -> m a -> m a
envSubst ss m = local (map (second (applySubst ss))) m

newTypeVar :: MonadState TCState m => m TypeVar
newTypeVar = state (\st -> let v = typeVarCounter st in (v, st {typeVarCounter = v+1}))

addVarNew v m = do
  tv <- newTypeVar
  t <- addVar v (TVar tv) m
  return (tv,t)

addConstraint :: Class -> TypeVar -> TC ()
addConstraint c v = do
  st <- get
  let ctxt = sortContext st
  put (st {sortContext = M.insertWith S.union v (S.singleton c) ctxt})

addSort :: S.Set Class -> TypeVar -> TC ()
addSort s v = do
  st <- get
  let ctxt = sortContext st
  put (st {sortContext = M.insertWith S.union v s ctxt})


getSort :: TypeVar -> TC (S.Set Class)
getSort v = do
  st <- get
  return (M.findWithDefault S.empty v (sortContext st))


infer :: Expr -> TC (Subst,Type)
infer Skip = return (M.empty, TIO tUnit)
infer (Var v) = do
  t <- lookupVar v
  return (M.empty,t)
infer (FromInteger i) = return (M.empty,tInt)
infer (BoolLit b) = return (M.empty,tBool)
infer (Abs e) = do
  (sub1,t) <- infer e
  a <- newTVarOfClass CNum
  sub2 <- unify t a
  return (sub2 |.| sub1, applySubst sub2 t)
infer (Signum e) = do
  (sub1,t) <- infer e
  a <- newTVarOfClass CNum
  sub2 <- unify t a
  return (sub2 |.| sub1, applySubst sub2 t)
infer (Tup2 e1 e2) = do
  (sub1,t1) <- infer e1
  (sub2,t2) <- envSubst sub1 $ infer e2
  return (sub2 |.| sub1, TTup2 t1 t2)
infer (Fst e) = do
  (sub1,t) <- infer e
  a <- liftM TVar newTypeVar
  sub2 <- unify t (TTup2 t a)
  return (sub2 |.| sub1, t)
infer (Snd e) = do
  (sub1,t) <- infer e
  a <- liftM TVar newTypeVar
  sub2 <- unify t (TTup2 a t)
  return (sub2 |.| sub1, t)
infer (Let v e1 e2) = do
  (sub1,t1) <- infer e1
  (sub2,t2) <- addVar v t1 $ envSubst sub1 $ infer e2
  return (sub2 |.| sub1, t2)
infer (BinOp op e1 e2) = do
  (sub1,t1) <- infer e1
  a <- typeFromBinOp op
  sub2 <- unify t1 a
  (sub3,t2) <- envSubst (sub2 |.| sub1) $ infer e2
  let sacc1 = sub3 |.| sub2 |.| sub1
  sub4 <- unify t2 $ applySubst sacc1 a
  let sacc2 = sub4 |.| sacc1
  return (sacc2, applySubst sacc2 t2)
infer (Compare op e1 e2) = do
  (sub1,t1) <- infer e1
  a <- typeFromCompOp op
  sub2 <- unify t1 a
  (sub3,t2) <- envSubst (sub2 |.| sub1) $ infer e2
  let sacc1 = sub3 |.| sub2 |.| sub1
  sub4 <- unify t2 $ applySubst sacc1 a
  return (sub4 |.| sacc1, tBool)
infer (Lambda v e) = do
  a <- liftM TVar newTypeVar
  (sub,t) <- addVar v a $ infer e
  return (sub, applySubst sub $ a --> t)
infer (Return e) = do
  (sub,t) <- infer e
  return (sub, TIO t)
infer (Bind e1 e2) = do
  (sub1,t1) <- infer e1
  a <- liftM TVar newTypeVar
  sub2 <- unify t1 (TIO a)
  (sub3,t2) <- envSubst (sub2 |.| sub1) $ infer e2
  b <- liftM TVar newTypeVar
  sub4 <- unify t2 $ applySubst (sub3 |.| sub2 |.| sub1) (a --> TIO b)
  let sub = sub4 |.| sub3 |.| sub2 |.| sub1
  return (sub, applySubst sub (TIO b))
infer (ParM e1 e2) = do
  (sub1,t1) <- infer e1
  sub2 <- unify t1 tInt
  (sub3,t2) <- envSubst (sub2 |.| sub1) $ infer e2
  unify t2 (tInt --> (TIO tUnit))
  return (sub3 |.| sub2 |.| sub1, TIO (tUnit))
infer (IterateWhile e1 e2 e3) = do
  s <- liftM TVar newTypeVar
  (sub1,t1) <- infer e1
  sub2 <- unify t1 (s --> tBool)
  let sacc1 = sub2 |.| sub1
  (sub3,t2) <- envSubst sacc1 $ infer e2
  let sacc2 = sub3 |.| sacc1
  sub4 <- unify t2 (applySubst sacc2 (s --> s))
  let sacc3 = sub4 |.| sacc2
  (sub5,t3) <- envSubst sacc3 $ infer e3
  let sacc4 = sub5 |.| sacc3
  sub6 <- unify t3 (applySubst sacc4 s)
  let sacc5 = sub6 |.| sacc4
  return (sacc5, applySubst sacc5 s)
infer (WhileM e1 e2 e3 e4) = do
  s <- liftM TVar newTypeVar
  (sub1,t1) <- infer e1
  sub2 <- unify t1 (s --> tBool)
  let sacc1 = sub2 |.| sub1
  (sub3,t2) <- envSubst sacc1 $ infer e2
  let sacc2 = sub3 |.| sacc1
  sub4 <- unify t2 $ applySubst sacc2 (s --> s)
  let sacc3 = sub4 |.| sacc2
  (sub5,t3) <- envSubst sacc3 $ infer e3
  let sacc4 = sub5 |.| sacc3
  sub6 <- unify t3 $ applySubst sacc4 (s --> TIO tUnit)
  let sacc5 = sub6 |.| sacc4
  (sub7,t4) <- envSubst sacc5 $ infer e4
  let sacc6 = sub7 |.| sacc5
  sub8 <- unify t4 $ applySubst sacc5 s
  return (sub8 |.| sacc6, TIO tUnit)
infer (RunMutableArray e) = do
  (sub1,t) <- infer e
  a <- liftM TVar newTypeVar
  sub2 <- unify t (TIO (TMArr a))
  let sub = sub2 |.| sub1
  return (sub, applySubst sub (TIArr a))
infer (ReadIArray e1 e2) = do
  (sub1,t1) <- infer e1
  a <- liftM TVar newTypeVar 
  sub2 <- unify t1 (TIArr a)
  (sub3,t2) <- envSubst (sub2 |.| sub1) $ infer e2
  sub4 <- unify t2 tInt
  let sub = sub4 |.| sub3 |.| sub2 |.| sub1
  return (sub, applySubst sub a)
infer (ArrayLength e) = do
  (sub1,t1) <- infer e
  a <- liftM TVar newTypeVar
  sub2 <- unify t1 (TIArr a)
  return (sub2 |.| sub1, tInt)
infer (NewArray e) = do
  (sub1,t1) <- infer e
  a <- liftM TVar newTypeVar
  sub2 <- unify t1 tInt
  let sub = sub2 |.| sub1
  return (sub, applySubst sub (TIO (TMArr a)))
infer (ReadArray e1 e2) = do
  (sub1,t1) <- infer e1
  a <- liftM TVar newTypeVar
  sub2 <- unify t1 (TMArr a)
  (sub3,t2) <- envSubst (sub2 |.| sub1) $ infer e2
  sub4 <- unify t2 tInt
  let sub = sub4 |.| sub3 |.| sub2 |.| sub1
  return (sub, applySubst sub (TIO a))
infer (WriteArray e1 e2 e3) = do
  (sub1,t1) <- infer e1
  a <- liftM TVar newTypeVar
  sub2 <- unify t1 (TMArr a)
  let sacc1 = sub2 |.| sub1
  (sub3,t2) <- envSubst sacc1 $ infer e2
  let sacc2 = sub3 |.| sacc1
  sub4 <- unify t2 tInt
  let sacc3 = sub4 |.| sacc2
  (sub5,t3) <- envSubst sacc3 $ infer e3
  let sacc4 = sub5 |.| sacc3
  sub6 <- unify t3 a
  let sacc5 = sub6 |.| sacc4
  return (sacc5, TIO tUnit)
infer (Print e1) = do
  a <- newTVarOfClass CShow
  (sub1,t1) <- infer e1
  sub2 <- unify t1 a
  return (sub2 |.| sub1, TIO tUnit)

newTVarOfClass :: Class -> TC Type
newTVarOfClass c = do
  a <- newTypeVar
  addConstraint c a
  return (TVar a)


typeFromBinOp :: BinOp -> TC Type
typeFromBinOp Plus  = newTVarOfClass CNum
typeFromBinOp Minus = newTVarOfClass CNum
typeFromBinOp Mult  = newTVarOfClass CNum
typeFromBinOp Quot  = newTVarOfClass CIntegral
typeFromBinOp Rem   = newTVarOfClass CIntegral
typeFromBinOp Min   = newTVarOfClass COrd
typeFromBinOp Max   = newTVarOfClass COrd
typeFromBinOp And   = return tBool
typeFromBinOp Or    = return tBool

typeFromCompOp EQU  = newTVarOfClass CEq
typeFromCompOp NEQ = newTVarOfClass CEq
typeFromCompOp GTH = newTVarOfClass COrd
typeFromCompOp LTH = newTVarOfClass COrd
typeFromCompOp GEQ = newTVarOfClass COrd
typeFromCompOp LEQ = newTVarOfClass COrd

classMatch :: Class -> Type -> Bool
classMatch CEq (TConst TInt) = True
classMatch CEq (TConst TBool) = True
classMatch CEq (TTup2 t1 t2) = (classMatch CEq t1) && (classMatch CEq t2)
classMatch CEq (TConst TUnit) = True
classMatch COrd (TConst TInt) = True
classMatch COrd (TConst TBool) = True
classMatch COrd (TTup2 t1 t2) = (classMatch COrd t1) && (classMatch COrd t2)
classMatch COrd (TConst TUnit) = True
classMatch CNum (TConst TInt) = True
classMatch CIntegral (TConst TInt) = True
classMatch CShow (TConst TInt) = True
classMatch CShow (TConst TBool) = True
classMatch CShow (TTup2 t1 t2) = (classMatch CShow t1) && (classMatch CShow t2)
classMatch CShow (TConst TUnit) = True
classMatch _ _ = False

sortMatch :: (S.Set Class) -> Type -> Bool
sortMatch s t = S.foldr (\c b -> (classMatch c t) && b) True s

unify :: Type -> Type -> TC Subst
unify (TVar v1) (TVar v2) | v1 == v2  = return M.empty
                          | otherwise = do 
  sort <- getSort v2
  addSort sort v1
  return (M.singleton v2 (TVar v1))
unify t (TVar v) | occurs v t = throwError ("infinite type: " ++ (show v) ++ " ~ " ++ (show t) ++ ".")
                 | otherwise  = do
  sort <- getSort v
  if sortMatch sort t
     then return (M.singleton v t)
     else throwError ("type: " ++ (show t) ++ " does not match sort " ++ (show sort) ++ ".")
unify (TVar v) s = unify s (TVar v)
unify (TConst t1) (TConst t2) | t1 == t2 = return M.empty
unify (TMArr t) (TMArr s) = unify t s
unify (TIArr t) (TIArr s) = unify t s
unify (TIO   t) (TIO   s) = unify t s
unify (TTup2 t1 t2) (TTup2 s1 s2) = do
  sub1 <- unify t1 s1
  sub2 <- unify (applySubst sub1 t2) (applySubst sub1 s2)
  return (sub2 |.| sub1)
unify (TFun t1 t2) (TFun s1 s2) = do
  sub1 <- unify t1 s1
  sub2 <- unify (applySubst sub1 t2) (applySubst sub1 s2)
  return (sub2 |.| sub1)
unify t s = throwError ("could not unify '" ++ (show t) ++ "' with '" ++ (show s) ++ "'.")


occurs :: TypeVar -> Type -> Bool
occurs v (TVar v') | v == v' = True
                   | v /= v' = False
occurs v (TMArr t) = occurs v t
occurs v (TIArr t) = occurs v t
occurs v (TIO   t) = occurs v t
occurs v (TTup2 t1 t2) = occurs v t1 || occurs v t2
occurs v (TFun  t1 t2) = occurs v t1 || occurs v t2
occurs v _ = False



