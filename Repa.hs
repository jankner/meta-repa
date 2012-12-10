{-# OPTIONS_GHC -fth #-}
{-# LANGUAGE GADTs, RankNTypes, FlexibleContexts #-}
module Repa where


import Data.Array.IO
import Data.Array.MArray

import Control.Arrow
import Control.Monad

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

  --Func2 :: (a -> b -> c) -> Expr a -> Expr b -> Expr c
  
  Return :: Expr a -> Expr (IO a)
  Bind   :: Expr (IO a) -> (Expr a -> Expr (IO b)) -> Expr (IO b)
  
  NewArray   :: MArray IOUArray a IO => Expr Int -> Expr (IO (IOUArray Int a))
  ReadArray  :: MArray IOUArray a IO => Expr (IOUArray Int a) -> Expr Int -> Expr (IO a)
  WriteArray :: MArray IOUArray a IO => Expr (IOUArray Int a) -> Expr Int -> Expr a -> Expr (IO ())
  ParM       :: Expr Int -> (Expr Int -> Expr (IO ())) -> Expr (IO ())
  Skip       :: Expr (IO ())

  Print :: Show a => Expr a -> Expr (IO ())


data Binop a where
  Plus  :: Binop a
  Mult  :: Binop a
  Minus :: Binop a
  
instance Num a => Num (Expr a) where
  (+) = Binop Plus
  (*) = Binop Mult
  (-) = Binop Minus
  abs = Abs
  signum = Signum
  fromInteger = FromInteger


data M a = M { unM :: forall b. ((a -> Expr (IO b)) -> Expr (IO b)) }
--data M a = M { unM :: ((a -> Expr (IO ())) -> Expr (IO ())) }

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

share :: Expr a -> M (Expr a)
share a = M (\k -> Return a `Bind` k)

printE :: Show a => Expr a -> M ()
printE a = M (\k -> Print a `Bind` (\_ -> k ()))

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

eval (Return a) = return (eval a)
eval (Bind m f) = (eval m) >>= (\a -> eval $ f (Value a))

eval (NewArray l)         = newArray_ (0, (eval l)-1)
eval (ReadArray arr i)    = readArray  (eval arr) (eval i)
eval (WriteArray arr i a) = writeArray (eval arr) (eval i) (eval a)

eval (ParM i body) = forM_ [0..(eval (i-1))] (\i -> eval (body (Value i)))
eval (Skip)        = return ()
eval (Print a)     = print (eval a)


showExpr :: Int -> Expr a -> String
showExpr i (Var v) = "x" ++ (show v)
showExpr i (Binop op a b)  = "(" ++ (showBinOp i op a b) ++ ")"
showExpr i (Abs a)         = "(abs " ++ (showExpr i a) ++ ")"
showExpr i (Signum a)      = "(signum " ++ (showExpr i a) ++ ")"
showExpr i (FromInteger n) = show n
showExpr i (Equal a b)     = "(" ++ (showExpr i a) ++ " == " ++ (showExpr i b) ++ ")"
showExpr i (NotEqual a b)     = "(" ++ (showExpr i a) ++ " /= " ++ (showExpr i b) ++ ")"
showExpr i (LTH a b)     = "(" ++ (showExpr i a) ++ " < " ++ (showExpr i b) ++ ")"
showExpr i (LTE a b)     = "(" ++ (showExpr i a) ++ " <= " ++ (showExpr i b) ++ ")"
showExpr i (GTH a b)     = "(" ++ (showExpr i a) ++ " > " ++ (showExpr i b) ++ ")"
showExpr i (GTE a b)     = "(" ++ (showExpr i a) ++ " >= " ++ (showExpr i b) ++ ")"
showExpr i (Max a b)     = "(max " ++ (showExpr i a) ++ " " ++ (showExpr i b) ++ ")"
showExpr i (Min a b)     = "(min " ++ (showExpr i a) ++ " " ++ (showExpr i b) ++ ")"
showExpr i (Return a)      = "(return " ++ (showExpr i a) ++ ")"
showExpr i (Bind m f)      = (showExpr i m) ++ " >>= " ++ (showExprFun i f)
showExpr i (NewArray l)          = "(newArray " ++ (showExpr i l) ++ ")"
showExpr i (ReadArray arr ix)    = "(readArray " ++ (showExpr i arr) ++ " " ++ (showExpr i ix) ++ ")"
showExpr i (WriteArray arr ix a) = "(writeArray " ++ (showExpr i arr) ++ " " ++ (showExpr i ix) ++ " " ++ (showExpr i a) ++ ")"
showExpr i (ParM n f) = "(parM " ++ (showExpr i n) ++ " " ++ (showExprFun i f) ++ ")"
showExpr i Skip = "skip"
showExpr i (Print a) = "(print " ++ (showExpr i a) ++ ")"


showExprFun :: Int -> (Expr a -> Expr b) -> String
showExprFun i f = "(\\x" ++ (show i) ++ " -> " ++ (showExpr (i+1) (f (Var i))) ++ ")"


showBinOp :: Int -> Binop a -> Expr a -> Expr a -> String
showBinOp i Minus a b = (showExpr i a) ++ " - " ++ (showExpr i b)
showBinOp i Plus  a b = (showExpr i a) ++ " + " ++ (showExpr i b)
showBinOp i Mult  a b = (showExpr i a) ++ " * " ++ (showExpr i b)


translate :: Expr a -> Q Exp
translate (Var2 n) = return $ VarE n

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

translate (Return a) = [|return $(translate a)|]
translate (Bind m f) = [| $(translate m)  >>= $(translateFunction f) |]

translate (NewArray l)          = [| newIOUArray (0, $(translate (l-1))) |]
translate (ReadArray arr ix)    = [| readArray $(translate arr) $(translate ix) |]
translate (WriteArray arr ix a) = [| writeArray $(translate arr) $(translate ix) $(translate a) |]
translate (ParM n f) = [| forM_ [0..($(translate (n-1)))] $(translateFunction f) |]
translate Skip       = [| return () |]
translate (Print a)  = [| print $(translate a) |]

translateFunction :: (Expr a -> Expr b) -> Q Exp
translateFunction f = 
  do x <- newName "x"
     fbody <- translate (f (Var2 x))
     return $ LamE [VarP x] fbody

newIOUArray :: MArray IOUArray a IO => (Int, Int) -> IO (IOUArray Int a)
newIOUArray = newArray_

{-
-- Pull arrays

data Pull a = Pull (Expr Int -> a) (Expr Int)

instance Functor Pull where
  fmap f (Pull ixf l) = Pull (f . ixf) l

enumPull :: Expr Int -> Expr Int -> Pull (Expr Int)
enumPull s e = Pull (\i -> s + i) (e - s)

storePull :: MArray IOUArray a IO => Pull (Expr a) -> M (Expr (IOUArray Int a))
storePull (Pull ixf l) = do arr <- newArrayE l
                            parM l (\i ->
                                     writeArrayE arr i (ixf i)
                                     )
                            return arr

-- Push

newtype P a = P { unP :: ((a -> Expr (IO ())) -> Expr (IO ())) }

instance Monad P where
  return a = P $ \k -> k a
  P f >>= g = P $ \k -> f (\a -> unP (g a) k)

instance Functor P where
  fmap f (P g) = P $ (\k -> g (k . f))

data Push a = Push (P (Expr Int, a)) (Expr Int)
--data Push a = Push (M (Expr Int,a)) (Expr Int)

instance Functor Push where
  fmap f (Push m l) = Push (fmap (second f) m) l

(+.+) :: Push a -> Push a -> Push a
Push m1 l1 +.+ Push m2 l2 = Push m (l1 + l2)
  where m = do m1
               indexT (l1 +) m2

indexT :: (Expr Int -> Expr Int) -> P (Expr Int,a) -> P (Expr Int,a)
indexT t m = do (i,a) <- m
                return (t i,a)


storePush :: MArray IOUArray a IO => Push (Expr a) -> M (Expr (IOUArray Int a))
storePush (Push m l) = do arr <- newArrayE l
                          M (\k -> unP m (\(i,a) -> WriteArray arr i a)
                                   `Bind` (\_ -> k ()))
                          return arr

pullToPush :: Pull a -> Push a
pullToPush (Pull ixf l) = Push m l
  where m = P (\k -> ParM l (\i -> k (i,ixf i) `Bind` (\_ -> Skip)))


ex :: M (Expr Int)
ex =
 do arr <- storePush $ pullToPush $ enumPull 0 9
    x <- readArrayE arr 5
    return x

ex2 = (storePush $ pullToPush $ enumPull 0 9) >>= (\arr -> readArrayE arr 5)

pex = Push (P (\k -> ParM 9 (\i -> k (i,i)))) 9
ex3 = storePush $ (pex) +.+ (pex)


test :: IO ()
test =
  do i <- eval $ (runM ex)
     print i
     x <- runQ (translate $ runM ex)
     putStrLn $ pprint x
     y <- eval $ runM ex3
     l <- getElems y
     print l
-}    

--Shapes



