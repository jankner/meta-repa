{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE Rank2Types #-}
module TypeCheck 
  ( TC
  , runTC
  , infer
  , annotate
  ) where

import FOASTyped
import FOASCommon
import Types

import Data.IORef
import qualified Data.Map as M
import qualified Data.Set as S

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.Error

import Control.Arrow


newtype TC a = TC { unTC :: ErrorT String (Reader Env) a }
  deriving (Monad,MonadReader Env,MonadError String)

runTC m = runReader (runErrorT (unTC m)) []


lookupVar :: (MonadError String m, MonadReader Env m) => Int -> m Type
lookupVar v = do
  mt <- reader (lookup v)
  case mt of
    Just t -> return t
    Nothing -> throwError ("unknown variable: " ++ (showVar v))

addVar :: MonadReader Env m => Int -> Type -> m a -> m a
addVar v t m = local ((v,t):) m


classMatch :: Class -> Type -> Bool
classMatch CEq (TConst _) = True
classMatch CEq (TTup2 t1 t2) = (classMatch CEq t1) && (classMatch CEq t2)
classMatch CEq (TTupN ts) | length ts <= 15 = foldl1 (&&) (map (classMatch CEq) ts)
classMatch COrd (TConst _) = True
classMatch COrd (TTup2 t1 t2) = (classMatch COrd t1) && (classMatch COrd t2)
classMatch COrd (TTupN ts) | length ts <= 15 = foldl1 (&&) (map (classMatch COrd) ts)
classMatch CNum (TConst TInt) = True
classMatch CNum (TConst TInt64) = True
classMatch CNum (TConst TWord) = True
classMatch CNum (TConst TWord64) = True
classMatch CNum (TConst TFloat) = True
classMatch CNum (TConst TDouble) = True
classMatch CIntegral (TConst TInt) = True
classMatch CIntegral (TConst TInt64) = True
classMatch CIntegral (TConst TWord) = True
classMatch CIntegral (TConst TWord64) = True
classMatch CFractional (TConst TFloat) = True
classMatch CFractional (TConst TDouble) = True
classMatch CFloating (TConst TFloat) = True
classMatch CFloating (TConst TDouble) = True
classMatch CBits (TConst TInt) = True
classMatch CBits (TConst TInt64) = True
classMatch CBits (TConst TWord) = True
classMatch CBits (TConst TWord64) = True
classMatch CShow (TConst _) = True
classMatch CShow (TTup2 t1 t2) = (classMatch CShow t1) && (classMatch CShow t2)
classMatch CShow (TTupN ts) | length ts <= 15 = foldl1 (&&) (map (classMatch CShow) ts)
classMatch _ _ = False


annotate :: Expr -> TC Expr
annotate = exprTraverse0 annotate' 

annotate' :: (Expr -> TC Expr) -> Expr -> TC Expr
annotate' k (Let v e1 e2) = do
  t <- infer e1
  e1' <- annotate' k e1
  e2' <- addVar v t $ annotate' k e2
  return $ LetAnn v t e1' e2'
annotate' k (Lambda v t0@(TFun t _) e) = do
  e' <- addVar v t $ annotate' k e
  return $ Lambda v t0 e'
annotate' k e | isAtomic e = return e
              | otherwise    = k e

infer :: Expr -> TC Type
infer Skip = return (TIO tUnit)
infer (Var v) = lookupVar v
infer e@(FromInteger t i) 
  | classMatch CNum t = return t
  | otherwise         = throwError ((show t) ++ " is not of class Num in expression: " ++ (show e))
infer e@(FromRational t r)
  | classMatch CFractional t = return t
  | otherwise                = throwError ((show t) ++ " is not of class Fractional in expression: " ++ (show e))
infer (FromIntegral tr s e) = do
  t <- infer e
  unless (classMatch CIntegral t) $
    throwError ("argument of 'fromIntegral' must be of class Integral in expression " ++ (show e) ++ ". actual type: " ++ (show t))
  unless (classMatch CNum tr) $
    throwError ("result type of 'fromIntegral' must be of class Num in expression " ++ (show (FromIntegral tr s e)) ++ ". actual type: " ++ (show tr))
  return tr
infer (Bit tr e) = do
  t <- infer e
  matchType2 e t tInt
  unless (classMatch CBits tr) $
    throwError ("result type of 'bit' must be of class Bits in expression " ++ (show (Bit tr e)) ++ ". actual type: " ++ (show tr))
  return tr
infer (Rotate _ e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  matchType2 e1 t1 tInt
  unless (classMatch CBits t2) $
    throwError ("argument of 'rotate' must be of class Integral in expression " ++ (show e2) ++ ". actual type: " ++ (show t2))
  return t2
infer (ShiftL _ e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  matchType2 e1 t1 tInt
  unless (classMatch CBits t2) $
    throwError ("argument of 'shiftL' must be of class Integral in expression " ++ (show e2) ++ ". actual type: " ++ (show t2))
  return t2
infer (ShiftR _ e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  matchType2 e1 t1 tInt
  unless (classMatch CBits t2) $
    throwError ("argument of 'shiftR' must be of class Integral in expression " ++ (show e2) ++ ". actual type: " ++ (show t2))
  return t2
infer (BoolLit b) = return tBool
infer (Unit) = return tUnit
infer (Tup2 e1 e2) = liftM2 TTup2 (infer e1) (infer e2)
infer (Fst _ e) = do
  t <- infer e
  case t of
    TTup2 t1 t2 -> return t1
    t' -> throwError ("expected tuple, actual type: " ++ (show t'))
infer (Snd _ e) = do
  t <- infer e
  case t of
    TTup2 t1 t2 -> return t2
    t' -> throwError ("expected tuple, actual type: " ++ (show t'))
infer (TupN es) = do
  ts <- mapM infer es
  return (TTupN ts)
infer (GetN _ i e) = do
  t <- infer e
  case t of
    TTupN ts -> return (ts !! i)
--    t' -> throwError("expected tuple of size " ++ (show n) ++ ". actual type: " ++ (show t'))
infer (Let v e1 e2) = do
  t1 <- infer e1
  t2 <- addVar v t1 $ infer e2
  return t2
infer (LetAnn v _ e1 e2) = do
  t1 <- infer e1
  t2 <- addVar v t1 $ infer e2
  return t2
infer (UnOp _ op e) = do
  t <- infer e
  checkUnOp op t
  return t
infer (BinOp _ op e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  when (t1 /= t2) $ throwError ("binop with operands of different type: " ++ (show t1) ++ " " ++ (show op) ++ " " ++ (show t2))
  checkBinOp op t1
  return t1
infer (Compare _ op e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  when (t1 /= t2) $ throwError ("compop with operands of different type: " ++ (show t1) ++ " " ++ (show op) ++ " " ++ (show t2))
  checkCompOp op t1
  return tBool
infer (App e1 _ e2) = do
  t1 <- infer e1
  t2 <- infer e2
  case t1 of
    TFun a b ->
      do matchType2 e2 t2 a
         return b
    _ -> throwError ("application to non-function expression: " ++ (show e1) ++ " :: " ++ (show t2))
infer (Lambda v (TFun t1 t2) e) = liftM (t1 -->) (addVar v t1 $ infer e)
infer (Return _ e) = do
  t <- infer e
  return (TIO t)
infer e@(Bind _ e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  case (t1,t2) of
    (TIO a, TFun a' (TIO b)) ->
      do matchType2 e a a'
         return (TIO b)
    _ -> throwError ((show e) ++ "\n ohno " ++ (show e1) ++ " :: " ++ (show t1) ++ " \n " ++ (show e2) ++ " :: "  ++ (show t2))
infer (ParM e1 e2) = do
  t1 <- infer e1
  when (t1 /= tInt) $ throwError "first argument of parM must be of type Int."
  t2 <- infer e2
  when (t2 /= (tInt --> TIO tUnit)) $ throwError ("second argument of parM must be of type IO -> IO (). actual type: " ++ (show t2) ++ " in expression: " ++ (show e2))
  return (TIO tUnit)
infer (If e1 e2 e3) = do
  t1 <- infer e1
  t2 <- infer e2
  t3 <- infer e3
  matchType2 e1 t1 tBool
  when (t2 /= t3) $ throwError ("types of branches in conditionals do not match: " ++ (show e1) ++ " :: " ++ (show t1) ++ " \n " ++ (show e2) ++ " :: "  ++ (show t2))
  return t2
infer (Rec _ e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  case t1 of 
    TFun (TFun a1 r1) (TFun a2 r2) 
      | a1 == a2 && r1 == r2 && t2 == a1 -> return r1
    _ -> throwError "type error in rec"
infer (IterateWhile _ e1 e2 e3) = do
  t1 <- infer e1
  t2 <- infer e2
  t3 <- infer e3
  matchType2 e1 t1 (t3 --> tBool)
  matchType2 e2 t2 (t3 --> t3)
  return t3
infer (WhileM _ e1 e2 e3 e4) = do
  t1 <- infer e1
  t2 <- infer e2
  t3 <- infer e3
  t4 <- infer e4
  matchType2 e1 t1 (t4 --> tBool)
  matchType2 e2 t2 (t4 --> t4)
  matchType2 e3 t3 (t4 --> TIO tUnit)
  return (TIO tUnit)
infer (RunMutableArray e) = do
  t <- infer e
  case t of
    TIO (TMArr a) -> return (TIArr a)
    _ -> throwError ("first argument of runMutableArray is not of type IO {a}. actual type: " ++ (show t))
infer (ReadIArray _ e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  matchType2 e2 t2 tInt
  case t1 of
    TIArr a -> return a
    _ -> throwError ("first argument of readIArray is not of type [a]. actual type: " ++ (show t1))
infer (ArrayLength e) = do
  t <- infer e
  case t of
    TIArr a -> return tInt
    _ -> throwError ("first argument of readIArray is not of type [a]. actual type: " ++ (show t))
infer (NewArray tr e) = do
  t <- infer e
  matchType2 e t tInt
  return (TIO (TMArr tr))
infer e@(ReadArray e1 e2) = do
  t1 <- infer e1
  t2 <- infer e2
  matchType2 e2 t2 tInt
  case t1 of
    TMArr a -> return (TIO a)
    _ -> throwError ("first argument of readArray is not of type {a}. actual type: " ++ (show t1))
infer (WriteArray _ e1 e2 e3) = do
  t1 <- infer e1
  t2 <- infer e2
  t3 <- infer e3
  matchType2 e2 t2 tInt
  case t1 of
    TMArr a ->
      do matchType2 e3 t3 a
         return (TIO tUnit)
    _ -> throwError ("first argument of writeArray is not of type {a}. actual type: " ++ (show t1))
infer (Print e) = do
  t <- infer e
  unless (classMatch CShow t) $ throwError ("type " ++ (show t) ++ " not of class Show.")
  return (TIO tUnit)

matchType :: Type -> Type -> TC Type
matchType t1 t2 | t1 == t2 = return t1
                | t1 /= t2 = throwError ("could not match " ++ (show t1) ++ " with " ++ (show t2))

matchType2 :: Expr -> Type -> Type -> TC Type
matchType2 e t1 t2 | t1 == t2 = return t1
                   | t1 /= t2 = throwError ("could not match " ++ (show t1) ++ " with " ++ (show t2) ++ " in experession: " ++ (show e))

checkBinOp :: BinOp -> Type -> TC ()
checkBinOp Plus  t | classMatch CNum t = return ()
checkBinOp Minus t | classMatch CNum t = return ()
checkBinOp Mult  t | classMatch CNum t = return ()
checkBinOp FDiv  t | classMatch CFractional t = return ()
checkBinOp Quot  t | classMatch CIntegral t = return ()
checkBinOp Rem   t | classMatch CIntegral t = return ()
checkBinOp Div   t | classMatch CIntegral t = return ()
checkBinOp Mod   t | classMatch CIntegral t = return ()
checkBinOp Min   t | classMatch COrd t = return ()
checkBinOp Max   t | classMatch COrd t = return ()
checkBinOp Xor   t | classMatch CBits t = return ()
checkBinOp BAnd  t | classMatch CBits t = return ()
checkBinOp BOr   t | classMatch CBits t = return ()
checkBinOp Pow   t | classMatch CFloating t = return ()
checkBinOp And   t | t == tBool = return ()
checkBinOp Or    t | t == tBool = return ()
checkBinOp op t = throwError ("type " ++ (show t) ++ " not compatible with operator " ++ (show op))

checkUnOp :: UnOp -> Type -> TC ()
checkUnOp Abs        t | classMatch CNum t = return ()
checkUnOp Signum     t | classMatch CNum t = return ()
checkUnOp Recip      t | classMatch CFractional t = return ()
checkUnOp Complement t | classMatch CBits t = return ()
checkUnOp Exp        t | classMatch CFloating t = return ()
checkUnOp Sqrt       t | classMatch CFloating t = return ()
checkUnOp Log        t | classMatch CFloating t = return ()
checkUnOp Sin        t | classMatch CFloating t = return ()
checkUnOp Tan        t | classMatch CFloating t = return ()
checkUnOp Cos        t | classMatch CFloating t = return ()
checkUnOp ASin       t | classMatch CFloating t = return ()
checkUnOp ATan       t | classMatch CFloating t = return ()
checkUnOp ACos       t | classMatch CFloating t = return ()
checkUnOp op     t = throwError ("type " ++ (show t) ++ " not compatible with operator " ++ (show op))

checkCompOp :: CompOp -> Type -> TC ()
checkCompOp EQU t | classMatch CEq t = return ()
checkCompOp NEQ t | classMatch CEq t = return ()
checkCompOp GTH t | classMatch COrd t = return ()
checkCompOp LTH t | classMatch COrd t = return ()
checkCompOp GEQ t | classMatch COrd t = return ()
checkCompOp LEQ t | classMatch COrd t = return ()
checkCompOp op t = throwError ("type " ++ (show t) ++ " not compatible with operator " ++ (show op))

