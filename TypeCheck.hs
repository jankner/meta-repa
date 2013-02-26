{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types #-}
module TypeCheck where

import FOAS
import qualified FOASTyped as T
import FOASCommon
import Types

import Data.IORef
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.ST

import Control.Arrow

data TCState = TCState { typeVarCounter :: Uniq, sortContext :: SortContext}
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


newTypeVar :: TC TypeVar
newTypeVar = 
  do v <- gets typeVarCounter
     modify (\st -> st {typeVarCounter = v+1})
     ref <- liftIO $ newIORef Nothing
     return (TypeVar v ref)

newTypeVarT :: TC Type
newTypeVarT = liftM TVar newTypeVar


readTVar :: TypeVar -> TC (Maybe Type)
readTVar = liftIO . readIORef . tRef

writeTVar :: TypeVar -> Type -> TC ()
writeTVar tv t = liftIO (writeIORef (tRef tv) (Just t))

zonkType :: Type -> TC Type
zonkType t@(TConst _) = return t
zonkType (TIO   t) = liftM TIO   (zonkType t)
zonkType (TMArr t) = liftM TMArr (zonkType t)
zonkType (TIArr t) = liftM TIArr (zonkType t)
zonkType (TTup2 t1 t2) = liftM2 TTup2 (zonkType t1) (zonkType t2)
zonkType (TFun  t1 t2) = liftM2 TFun  (zonkType t1) (zonkType t2)
zonkType (TVar tv) = do
  mt <- readTVar tv
  case mt of
    Just t  -> 
      do t' <- zonkType t
         writeTVar tv t'
         return t'
    Nothing -> return (TVar tv)

zonkType2 :: Type -> TC Type
zonkType2 t@(TConst _) = return t
zonkType2 (TIO   t) = liftM TIO   (zonkType2 t)
zonkType2 (TMArr t) = liftM TMArr (zonkType2 t)
zonkType2 (TIArr t) = liftM TIArr (zonkType2 t)
zonkType2 (TTup2 t1 t2) = liftM2 TTup2 (zonkType2 t1) (zonkType2 t2)
zonkType2 (TFun  t1 t2) = liftM2 TFun  (zonkType2 t1) (zonkType2 t2)
zonkType2 (TVar tv) = do
  mt <- readTVar tv
  case mt of
    Just t  -> 
      do t' <- zonkType2 t
         return t'
    Nothing -> return (TVar tv)

addConstraint :: Class -> TypeVar -> TC ()
addConstraint c tv = do
  st <- get
  let ctxt = sortContext st
  put (st {sortContext = M.insertWith S.union (uniq tv) (S.singleton c) ctxt})

addSort :: S.Set Class -> TypeVar -> TC ()
addSort s tv = do
  st <- get
  let ctxt = sortContext st
  put (st {sortContext = M.insertWith S.union (uniq tv) s ctxt})


getSort :: TypeVar -> TC (S.Set Class)
getSort tv = do
  st <- get
  return (M.findWithDefault S.empty (uniq tv) (sortContext st))

infer2 e = infer e >>= zonkType

infer :: Expr -> TC Type
infer Skip = return (TIO tUnit)
infer (Var v) = do
  t <- lookupVar v
  return t
infer (FromInteger i) = return tInt
infer (BoolLit b) = return tBool
infer (Abs e) = do
  t <- infer e
  a <- newTVarOfClass CNum
  unify t a
  return t
infer (Signum e) = do
  t <- infer e
  a <- newTVarOfClass CNum
  unify t a
  return t
infer (Tup2 e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  return (TTup2 t1 t2)
infer (Fst e) = do
  t <- infer e
  a <- newTypeVarT
  b <- newTypeVarT
  unify t (TTup2 a b)
  return a
infer (Snd e) = do
  t <- infer e
  a <- newTypeVarT
  b <- newTypeVarT
  unify t (TTup2 a b)
  return b
infer (Let v e1 e2) = do
  t1 <- infer e1
  t2 <- addVar v t1 $ infer e2
  return t2
infer (BinOp op e1 e2) = do
  t1 <- infer e1
  a <- typeFromBinOp op
  unify t1 a
  t2 <- infer e2
  unify t2 a
  return t2
infer (Compare op e1 e2) = do
  t1 <- infer e1
  a <- typeFromCompOp op
  unify t1 a
  t2 <- infer e2
  unify t2 a
  return tBool
infer (Lambda v e) = do
  a <- newTypeVarT
  t <- addVar v a $ infer e
  return (a --> t)
infer (Return e) = do
  t <- infer e
  return (TIO t)
infer (Bind e1 e2) = do
  t1 <- infer e1
  a <- newTypeVarT
  unify t1 (TIO a)
  t2 <- infer e2
  b <- newTypeVarT
  unify t2 (a --> TIO b)
  return (TIO b)
infer (ParM e1 e2) = do
  t1 <- infer e1
  unify t1 tInt
  t2 <- infer e2
  unify t2 (tInt --> (TIO tUnit))
  return (TIO tUnit)
infer (IterateWhile e1 e2 e3) = do
  s <- newTypeVarT
  t1 <- infer e1
  unify t1 (s --> tBool)
  t2 <- infer e2
  unify t2 (s --> s)
  t3 <- infer e3
  unify t3 s
  return s
infer (WhileM e1 e2 e3 e4) = do
  s <- newTypeVarT
  t1 <- infer e1
  unify t1 (s --> tBool)
  t2 <- infer e2
  unify t2 (s --> s)
  t3 <- infer e3
  unify t3 (s --> TIO tUnit)
  t4 <- infer e4
  unify t4 s
  return (TIO tUnit)
infer (RunMutableArray e) = do
  t <- infer e
  a <- newTypeVarT
  unify t (TIO (TMArr a))
  return (TIArr a)
infer (ReadIArray e1 e2) = do
  t1 <- infer e1
  a <- newTypeVarT
  unify t1 (TIArr a)
  t2 <- infer e2
  unify t2 tInt
  return a
infer (ArrayLength e) = do
  t1 <- infer e
  a <- newTypeVarT
  unify t1 (TIArr a)
  return tInt
infer (NewArray e) = do
  t1 <- infer e
  a <- newTypeVarT
  unify t1 tInt
  return (TIO (TMArr a))
infer (ReadArray e1 e2) = do
  t1 <- infer e1
  a <- newTypeVarT
  unify t1 (TMArr a)
  t2 <- infer e2
  unify t2 tInt
  return (TIO a)
infer (WriteArray e1 e2 e3) = do
  t1 <- infer e1
  a <- newTypeVarT
  unify t1 (TMArr a)
  t2 <- infer e2
  unify t2 tInt
  t3 <- infer e3
  unify t3 a
  return (TIO tUnit)
infer (Print e1) = do
  a <- newTVarOfClass CShow
  t1 <- infer e1
  unify t1 a
  return (TIO tUnit)

newTVarOfClass :: Class -> TC Type
newTVarOfClass c = do
  tv <- newTypeVar
  addConstraint c tv
  return (TVar tv)


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

typeFromCompOp EQU = newTVarOfClass CEq
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

unify :: Type -> Type -> TC ()
unify (TVar tv1) t2@(TVar tv2)
  | tv1 == tv2  = return ()
  | otherwise = unifyVar tv1 t2
unify t (TVar tv) = unifyVar tv t
unify (TVar tv) s = unifyVar tv s
unify (TConst t1) (TConst t2) | t1 == t2 = return ()
unify (TMArr t) (TMArr s) = unify t s
unify (TIArr t) (TIArr s) = unify t s
unify (TIO   t) (TIO   s) = unify t s
unify (TTup2 t1 t2) (TTup2 s1 s2) = do
  unify t1 s1
  unify t2 s2
unify (TFun t1 t2) (TFun s1 s2) = do
  unify t1 s1
  unify t2 s2
unify t s = throwError ("could not unify '" ++ (show t) ++ "' with '" ++ (show s) ++ "'.")


unifyVar :: TypeVar -> Type -> TC ()
unifyVar tv1 t2 = do
  mt1 <- readTVar tv1
  case mt1 of
    Just t1 -> unify t1 t2
    Nothing -> unifyUnbound tv1 t2

unifyUnbound :: TypeVar -> Type -> TC ()
unifyUnbound tv1 t2@(TVar tv2) = do
  mt2 <- readTVar tv2
  case mt2 of
    Just t2' -> unify (TVar tv1) t2'
    Nothing  -> do sort <- getSort tv2
                   addSort sort tv1
                   writeTVar tv1 t2
unifyUnbound tv1 t2 = do
  t2' <- zonkType t2
  sort <- getSort tv1
  when (occurs tv1 t2') $ throwError ("infinite type: " ++ (show tv1) ++ " = " ++ (show t2') ++ ".")
  unless (sortMatch sort t2') $ throwError ("could not match " ++ (show t2') ++ " with " ++ (show sort) ++ ".")
  writeTVar tv1 t2
      

occurs :: TypeVar -> Type -> Bool
occurs v (TVar v') | v == v' = True
                   | v /= v' = False
occurs v (TMArr t) = occurs v t
occurs v (TIArr t) = occurs v t
occurs v (TIO   t) = occurs v t
occurs v (TTup2 t1 t2) = occurs v t1 || occurs v t2
occurs v (TFun  t1 t2) = occurs v t1 || occurs v t2
occurs v _ = False

zonkExpr :: T.Expr -> TC T.Expr
zonkExpr = T.exprTraverse0 zonkExpr'

zonkExpr' k (T.FromInteger i t) = liftM (T.FromInteger i) (zonkType t)
zonkExpr' k (T.Lambda v t e) = do
  t' <- zonkType t
  e' <- k e
  return (T.Lambda v t' e')
zonkExpr' k e | T.isAtomic e = return e
              | otherwise    = k e

inferT :: Expr -> TC (T.Expr,Type)
inferT e =
  do (e,t) <- inferT1 e
     e' <- zonkExpr e
     t' <- zonkType t
     return (e',t')

inferT1 :: Expr -> TC (T.Expr,Type)
inferT1 Skip = return (T.Skip, TIO tUnit)
inferT1 (Var v) = do
  t <- lookupVar v
  return (T.Var v, t)
inferT1 (FromInteger i) = do
  a <- newTVarOfClass CNum
  return (T.FromInteger i a, a)
inferT1 (BoolLit b) = return (T.BoolLit b, tBool)
inferT1 (Abs e) = do
  (e',t) <- inferT1 e
  a <- newTVarOfClass CNum
  unify2 e t a
  return (T.Abs e', t)
inferT1 (Signum e) = do
  (e',t) <- inferT1 e
  a <- newTVarOfClass CNum
  unify2 e t a
  return (T.Signum e', t)
inferT1 (Tup2 e1 e2) = do
  (e1',t1) <- inferT1 e1
  (e2',t2) <- inferT1 e2
  return (T.Tup2 e1' e2', (TTup2 t1 t2))
inferT1 (Fst e) = do
  (e',t) <- inferT1 e
  a <- newTypeVarT
  b <- newTypeVarT
  unify2 e t (TTup2 a b)
  return (T.Fst e', a)
inferT1 (Snd e) = do
  (e',t) <- inferT1 e
  a <- newTypeVarT
  b <- newTypeVarT
  unify2 e t (TTup2 a b)
  return (T.Snd e',b)
inferT1 (Let v e1 e2) = do
  (e1',t1) <- inferT1 e1
  (e2',t2) <- addVar v t1 $ inferT1 e2
  return (T.Let v e1' e2', t2)
inferT1 (BinOp op e1 e2) = do
  (e1',t1) <- inferT1 e1
  a <- typeFromBinOp op
  unify2 e1 t1 a
  (e2',t2) <- inferT1 e2
  unify2 e2 t2 a
  return (T.BinOp op e1' e2', t2)
inferT1 (Compare op e1 e2) = do
  (e1',t1) <- inferT1 e1
  a <- typeFromCompOp op
  unify2 e1 t1 a
  (e2',t2) <- inferT1 e2
  unify2 e2 t2 a
  return (T.Compare op e1' e2', tBool)
inferT1 (Lambda v e) = do
  a <- newTypeVarT
  (e', t) <- addVar v a $ inferT1 e
  return (T.Lambda v a e', a --> t)
inferT1 (Return e) = do
  (e', t) <- inferT1 e
  return (T.Return e', TIO t)
inferT1 (Bind e1 e2) = do
  (e1', t1) <- inferT1 e1
  a <- newTypeVarT
  unify2 e1 t1 (TIO a)
  (e2', t2) <- inferT1 e2
  b <- newTypeVarT
  unify2 e2 t2 (a --> TIO b)
  return (T.Bind e1' e2', TIO b)
inferT1 (ParM e1 e2) = do
  (e1', t1) <- inferT1 e1
  unify2 e1 t1 tInt
  (e2', t2) <- inferT1 e2
  unify2 e2 t2 (tInt --> (TIO tUnit))
  return (T.ParM e1' e2', TIO tUnit)
inferT1 (IterateWhile e1 e2 e3) = do
  s <- newTypeVarT
  (e1', t1) <- inferT1 e1
  unify2 e1 t1 (s --> tBool)
  (e2', t2) <- inferT1 e2
  unify2 e2 t2 (s --> s)
  (e3', t3) <- inferT1 e3
  unify2 e3 t3 s
  return (T.IterateWhile e1' e2' e3', s)
inferT1 (WhileM e1 e2 e3 e4) = do
  s <- newTypeVarT
  (e1', t1) <- inferT1 e1
  unify2 e1 t1 (s --> tBool)
  (e2', t2) <- inferT1 e2
  unify2 e2 t2 (s --> s)
  (e3', t3) <- inferT1 e3
  unify2 e3 t3 (s --> TIO tUnit)
  (e4', t4) <- inferT1 e4
  unify2 e4 t4 s
  return (T.WhileM e1' e2' e3' e4', TIO tUnit)
inferT1 (RunMutableArray e) = do
  (e', t) <- inferT1 e
  a <- newTypeVarT
  unify2 e t (TIO (TMArr a))
  return (T.RunMutableArray e', TIArr a)
inferT1 (ReadIArray e1 e2) = do
  (e1', t1) <- inferT1 e1
  a <- newTypeVarT
  unify2 e1 t1 (TIArr a)
  (e2', t2) <- inferT1 e2
  unify2 e2 t2 tInt
  return (T.ReadIArray e1' e2', a)
inferT1 (ArrayLength e) = do
  (e', t) <- inferT1 e
  a <- newTypeVarT
  unify2 e t (TIArr a)
  return (T.ArrayLength e', tInt)
inferT1 (NewArray e) = do
  (e', t) <- inferT1 e
  a <- newTypeVarT
  unify2 e t tInt
  return (T.NewArray e', TIO (TMArr a))
inferT1 (ReadArray e1 e2) = do
  (e1', t1) <- inferT1 e1
  a <- newTypeVarT
  unify2 e1 t1 (TMArr a)
  (e2', t2) <- inferT1 e2
  unify2 e2 t2 tInt
  return (T.ReadArray e1' e2', TIO a)
inferT1 (WriteArray e1 e2 e3) = do
  (e1', t1) <- inferT1 e1
  a <- newTypeVarT
  unify2 e1 t1 (TMArr a)
  (e2', t2) <- inferT1 e2
  unify2 e2 t2 tInt
  (e3', t3) <- inferT1 e3
  unify2 e3 t3 a
  return (T.WriteArray e1' e2' e3', TIO tUnit)
inferT1 (Print e) = do
  a <- newTVarOfClass CShow
  (e', t) <- inferT1 e
  unify2 e t a
  return (T.Print e', TIO tUnit)

unify2 e t1 t2 =
  catchError (unify t1 t2) (\err ->
    throwError (err ++ "\nin expression: " ++ (show e)))

newtype TC2 a = TC2 { unTC2 :: ErrorT String (Reader Env) a }
  deriving (Monad,MonadReader Env,MonadError String)

runTC2 m = runReader (runErrorT (unTC2 m)) []

inferT2 :: T.Expr -> TC2 Type
inferT2 T.Skip = return (TIO tUnit)
inferT2 (T.Var v) = lookupVar v
inferT2 (T.FromInteger i t) = return t
inferT2 (T.BoolLit b) = return tBool
inferT2 (T.Abs e) = inferT2 e
inferT2 (T.Signum e) = inferT2 e
inferT2 (T.Tup2 e1 e2) = liftM2 TTup2 (inferT2 e1) (inferT2 e2)
inferT2 (T.Fst e) = do
  t <- inferT2 e
  case t of
    TTup2 t1 t2 -> return t1
    t' -> throwError ("expected tuple, actual type: " ++ (show t'))
inferT2 (T.Snd e) = do
  t <- inferT2 e
  case t of
    TTup2 t1 t2 -> return t2
    t' -> throwError ("expected tuple, actual type: " ++ (show t'))
inferT2 (T.Let v e1 e2) = do
  t1 <- inferT2 e1
  t2 <- addVar v t1 $ inferT2 e2
  return t2
inferT2 (T.BinOp op e1 e2) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  when (t1 /= t2) $ throwError ("binop with operands of different type: " ++ (show t1) ++ " " ++ (show op) ++ " " ++ (show t2))
  checkBinOp op t1
  return t1
inferT2 (T.Compare op e1 e2) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  when (t1 /= t2) $ throwError ("compop with operands of different type: " ++ (show t1) ++ " " ++ (show op) ++ " " ++ (show t2))
  checkCompOp op t1
  return t1
inferT2 (T.Lambda v t e) = liftM (t -->) (addVar v t $ inferT2 e)
inferT2 (T.Return e) = do
  t <- inferT2 e
  return (TIO t)
inferT2 e@(T.Bind e1 e2) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  case (t1,t2) of
    (TIO a, TFun a' (TIO b)) ->
      do matchType a a'
         return (TIO b)
    _ -> throwError ((show e) ++ " ohno " ++ (show e1) ++ " :: " ++ (show t1) ++ " \n " ++ (show e2) ++ " :: "  ++ (show t2))
inferT2 (T.ParM e1 e2) = do
  t1 <- inferT2 e1
  when (t1 /= tInt) $ throwError "first argument of parM must be of type Int."
  t2 <- inferT2 e2
  when (t2 /= (tInt --> TIO tUnit)) $ throwError ("second argument of parM must be of type IO -> IO (). actual type: " ++ (show t2) ++ " in expression: " ++ (show e2))
  return (TIO tUnit)
inferT2 (T.IterateWhile e1 e2 e3) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  t3 <- inferT2 e3
  matchType t1 (t3 --> tBool)
  matchType t2 (t3 --> t3)
  return t3
inferT2 (T.WhileM e1 e2 e3 e4) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  t3 <- inferT2 e3
  t4 <- inferT2 e4
  matchType t1 (t4 --> tBool)
  matchType t2 (t4 --> t4)
  matchType t3 (t4 --> TIO tUnit)
  return (TIO tUnit)
inferT2 (T.RunMutableArray e) = do
  t <- inferT2 e
  case t of
    TIO (TMArr a) -> return (TIArr a)
    _ -> throwError ("first argument of runMutableArray is not of type IO {a}. actual type: " ++ (show t))
inferT2 (T.ReadIArray e1 e2) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  matchType t2 tInt
  case t1 of
    TIArr a -> return a
    _ -> throwError ("first argument of readIArray is not of type [a]. actual type: " ++ (show t1))
inferT2 (T.ArrayLength e) = do
  t <- inferT2 e
  case t of
    TIArr a -> return a
    _ -> throwError ("first argument of readIArray is not of type [a]. actual type: " ++ (show t))
inferT2 (T.NewArray e) = do
  t <- inferT2 e
  matchType t tInt
  return (TIO (TMArr t))
inferT2 e@(T.ReadArray e1 e2) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  matchType t2 tInt
  case t1 of
    TMArr a -> return (TIO a)
    _ -> throwError ("first argument of readArray is not of type {a}. actual type: " ++ (show t1))
inferT2 (T.WriteArray e1 e2 e3) = do
  t1 <- inferT2 e1
  t2 <- inferT2 e2
  t3 <- inferT2 e3
  matchType t2 tInt
  case t1 of
    TMArr a ->
      do matchType a t3
         return (TIO tUnit)
    _ -> throwError ("first argument of writeArray is not of type {a}. actual type: " ++ (show t1))
inferT2 (T.Print e) = do
  t <- inferT2 e
  unless (classMatch CShow t) $ throwError ("type " ++ (show t) ++ " not of class Show.")
  return (TIO tUnit)

matchType :: Type -> Type -> TC2 Type
matchType t1 t2 | t1 == t2 = return t1
                | t1 /= t2 = throwError ("could not match " ++ (show t1) ++ " with " ++ (show t2))


checkBinOp :: BinOp -> Type -> TC2 ()
checkBinOp Plus  t | classMatch CNum t = return ()
checkBinOp Minus t | classMatch CNum t = return ()
checkBinOp Mult  t | classMatch CNum t = return ()
checkBinOp Quot  t | classMatch CIntegral t = return ()
checkBinOp Rem   t | classMatch CIntegral t = return ()
checkBinOp Min   t | classMatch COrd t = return ()
checkBinOp Max   t | classMatch COrd t = return ()
checkBinOp And   t | t == tBool = return ()
checkBinOp Or    t | t == tBool = return ()
checkBinOp op t = throwError ("type " ++ (show t) ++ " not compatible with operator " ++ (show op))

checkCompOp :: CompOp -> Type -> TC2 ()
checkCompOp EQU t | classMatch CEq t = return ()
checkCompOp NEQ t | classMatch CEq t = return ()
checkCompOp GTH t | classMatch COrd t = return ()
checkCompOp LTH t | classMatch COrd t = return ()
checkCompOp GEQ t | classMatch COrd t = return ()
checkCompOp LEQ t | classMatch COrd t = return ()
checkCompOp op t = throwError ("type " ++ (show t) ++ " not compatible with operator " ++ (show op))

