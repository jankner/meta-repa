{-# OPTIONS_GHC -fth #-}
{-# LANGUAGE GADTs, RankNTypes, FlexibleContexts, FlexibleInstances, TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
module HOAS where


import Data.Array.IO hiding (unsafeFreeze)
import Data.Array.MArray hiding (unsafeFreeze)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.Unsafe

import Data.Int
import Data.Word
import Data.List
import Data.Maybe

import Control.Arrow
import Control.Monad
import Control.Monad.Reader
import Control.Monad.State

import System.IO.Unsafe

import Language.Haskell.TH hiding (Type)

data Type a where
  TConst :: TypeConst a -> Type a
  TTup2 :: Type a -> Type b -> Type (a,b)
  TTupN :: Tup t => t Type -> Type (t Id)
  TMArr :: Type a -> Type (IOUArray Int a)
  TIArr :: Type a -> Type (UArray Int a)
  TFun :: Type a -> Type b -> Type (a -> b)
  TIO :: Type a -> Type (IO a)
  

data TypeConst a where
  TInt :: TypeConst Int
  TInt64 :: TypeConst Int64
  TWord :: TypeConst Word
  TWord64 :: TypeConst Word64
  TDouble :: TypeConst Double
  TFloat :: TypeConst Float
  TBool :: TypeConst Bool

deriving instance Show (TypeConst a)

class (MArray IOUArray a IO, IArray UArray a) => Storable a where
  typeConstOf :: a -> TypeConst a
  typeConstOf0 :: TypeConst a

instance Storable Int where
  typeConstOf _ = TInt
  typeConstOf0  = TInt

instance Storable Int64 where
  typeConstOf _ = TInt64
  typeConstOf0  = TInt64

instance Storable Word where
  typeConstOf _ = TWord
  typeConstOf0  = TWord

instance Storable Word64 where
  typeConstOf _ = TWord64
  typeConstOf0  = TWord64

instance Storable Double where
  typeConstOf _ = TDouble
  typeConstOf0  = TDouble

instance Storable Float where
  typeConstOf _ = TFloat
  typeConstOf0  = TFloat

instance Storable Bool where
  typeConstOf _ = TBool
  typeConstOf0  = TBool

class Typeable a where
  typeOf :: a -> Type a
  typeOf0 :: Type a

instance Typeable Int where
  typeOf _ = TConst TInt
  typeOf0  = TConst TInt

instance Typeable Int64 where
  typeOf _ = TConst TInt64
  typeOf0  = TConst TInt64

instance Typeable Word where
  typeOf _ = TConst TWord
  typeOf0  = TConst TWord

instance Typeable Word64 where
  typeOf _ = TConst TWord64
  typeOf0  = TConst TWord64

instance Typeable Float where
  typeOf _ = TConst TFloat
  typeOf0  = TConst TFloat

instance Typeable Double where
  typeOf _ = TConst TDouble
  typeOf0  = TConst TDouble

instance Typeable Bool where
  typeOf _ = TConst TBool
  typeOf0  = TConst TBool

instance (Typeable a, Typeable b) => Typeable (a,b) where
  typeOf _ = TTup2 (typeOf0 :: Type a) (typeOf0 :: Type b)
  typeOf0  = TTup2 (typeOf0 :: Type a) (typeOf0 :: Type b)

data Z = Z
data S n = S n

nat1 = S Z
nat2 = S nat1
nat3 = S nat2
nat4 = S nat3
nat5 = S nat4
nat6 = S nat5
nat7 = S nat6
nat8 = S nat7
nat9 = S nat8

class Nat n where
  natToInt :: n -> Int

instance Nat Z where
  natToInt _ = 0

instance Nat n => Nat (S n) where
  natToInt (S n) = 1 + natToInt n

infixr 3 ::.

newtype Id t = Id { unId :: t}

data Ein a m = Ein (m a)
  deriving Show
data Cons a as m = (m a) ::. (as m)
  deriving Show

class Tup (t :: (* -> *) -> *) where
  tupLen :: t m -> Int
  tupMap :: (forall a. m a -> b) -> t m -> [b]
  tupFake :: t m

instance Tup (Ein a) where
  tupLen _ = 1
  tupMap f (Ein a) = [f a]
  tupFake = Ein undefined

instance Tup as => Tup (Cons a as) where
  tupLen (a ::. as) = 1 + tupLen as
  tupMap f (a ::. as) = f a : (tupMap f as)
  tupFake = undefined ::. tupFake

tupTail :: Tup as => (Cons a as m) -> as m
tupTail (a ::. as) = as

class (Nat n, Tup t) => Get n t m a | n t -> a where
  tupGet :: n -> t m -> m a

instance Get Z (Ein a) m a where
  tupGet Z (Ein a) = a

instance Tup as => Get Z (Cons a as) m a where
  tupGet Z (a ::. as) = a

instance Get n as m b => Get (S n) (Cons a as) m b where
  tupGet (S n) (a ::. as) = tupGet n as



instance Show (Expr a) where
  show = showExpr 0

data Expr a where
  Var   :: Int -> Expr a
  Var2  :: Name -> Expr a
  Value :: a -> Expr a

  Binop :: Binop a -> Expr a -> Expr a -> Expr a
  Abs :: Num a => Expr a -> Expr a
  Signum :: Num a => Expr a -> Expr a
  Recip :: Fractional a => Expr a -> Expr a
  FromInteger :: Num a => TypeConst a -> Integer -> Expr a
  FromRational :: Fractional a => TypeConst a -> Rational -> Expr a
  FromIntegral :: (Integral a, Num b) => Type b -> Expr a -> Expr b

  BoolLit :: Bool -> Expr Bool

  Equal :: Eq a => Expr a -> Expr a -> Expr Bool
  NotEqual :: Eq a => Expr a -> Expr a -> Expr Bool

  GTH :: Ord a => Expr a -> Expr a -> Expr Bool
  LTH :: Ord a => Expr a -> Expr a -> Expr Bool
  GTE :: Ord a => Expr a -> Expr a -> Expr Bool
  LTE :: Ord a => Expr a -> Expr a -> Expr Bool

  Tup2 :: Expr a -> Expr b -> Expr (a,b)
  Fst :: Expr (a,b) -> Expr a
  Snd :: Expr (a,b) -> Expr b

  TupN :: (Tup t) => t Expr -> Expr (t Id)
  GetN :: (Get n t Expr b) => Int -> n -> Expr (t Id) -> Expr b

  Let :: Expr a -> (Expr a -> Expr b) -> Expr b

  Return :: Expr a -> Expr (IO a)
  Bind   :: Expr (IO a) -> (Expr a -> Expr (IO b)) -> Expr (IO b)

  If :: Expr Bool -> Expr a -> Expr a -> Expr a

  IterateWhile :: (Expr s -> Expr Bool) -> (Expr s -> Expr s) -> Expr s -> Expr s
  WhileM :: (Expr s -> Expr Bool) -> (Expr s -> Expr s) -> (Expr s -> Expr (IO ())) -> Expr s -> Expr (IO ())

  RunMutableArray :: Storable a => Expr (IO (IOUArray Int a)) -> Expr (UArray Int a)
  ReadIArray :: Storable a => Expr (UArray Int a) -> Expr Int -> Expr a
  ArrayLength :: Storable a => Expr (UArray Int a) -> Expr Int

  NewArray   :: Storable a => Expr Int -> Expr (IO (IOUArray Int a))
  ReadArray  :: Storable a => Expr (IOUArray Int a) -> Expr Int -> Expr (IO a)
  WriteArray :: Storable a => Expr (IOUArray Int a) -> Expr Int -> Expr a -> Expr (IO ())
  ParM       :: Expr Int -> (Expr Int -> Expr (IO ())) -> Expr (IO ())
  Skip       :: Expr (IO ())

  Print :: Show a => Expr a -> Expr (IO ())


data Binop a where
  Plus  :: Num a => Binop a
  Mult  :: Num a => Binop a
  Minus :: Num a => Binop a
  Min   :: Ord a => Binop a
  Max   :: Ord a => Binop a
  Quot  :: Integral a => Binop a
  Rem   :: Integral a => Binop a
  Div   :: Integral a => Binop a
  Mod   :: Integral a => Binop a
  FDiv  :: Fractional a => Binop a
  And   :: Binop Bool
  Or    :: Binop Bool

deriving instance Eq (Binop a)

instance (Storable a, Num a) => Num (Expr a) where
  (FromInteger t 0) + e                 = e
  e                 + (FromInteger t 0) = e
  e1 + e2 = Binop Plus e1 e2
  (FromInteger t 1) * e                 = e
  e                 * (FromInteger t 1) = e
  (FromInteger t 0) * e2                = 0
  e1                * (FromInteger t 0) = 0
  e1 * e2 = Binop Mult e1 e2
  e                 - (FromInteger t 0) = e
  e1 - e2 = Binop Minus e1 e2
  abs = Abs
  signum = Signum
  fromInteger = FromInteger typeConstOf0


instance (Storable a, Fractional a) => Fractional (Expr a) where
  (/) = Binop FDiv
  recip = Recip
  fromRational = FromRational typeConstOf0

getN :: Get n t Expr b => n -> Expr (t Id) -> Expr b
getN n et = GetN (tupLen (fake et)) n et
  where fake :: Tup t => Expr (t Id) -> t Id
        fake _ = tupFake

data M a = M { unM :: forall b. ((a -> Expr (IO b)) -> Expr (IO b)) }

instance Monad M where
  return a = M $ \k -> k a
  M f >>= g = M $ \k -> f (\a -> unM (g a) k)

instance Functor M where
  fmap f (M g) = M (\k -> g (k . f))

runM :: M (Expr a) -> Expr (IO a)
runM (M f) = f Return

newArrayE :: Storable a => Expr Int -> M (Expr (IOUArray Int a))
newArrayE i = M (\k -> NewArray i `Bind` k)

parM :: Expr Int -> (Expr Int -> M ()) -> M ()
parM l body = M (\k -> ParM l (\i -> unM (body i) (\() -> Skip))
                       `Bind` (\_ -> k ()))

writeArrayE :: Storable a => Expr (IOUArray Int a) -> Expr Int -> Expr a -> M ()
writeArrayE arr i a = M (\k -> WriteArray arr i a `Bind` (\_ -> k ()))

readArrayE :: Storable a => Expr (IOUArray Int a) -> Expr Int -> M (Expr a)
readArrayE arr i = M (\k -> ReadArray arr i `Bind` k)

readIArray :: Storable a => Expr (UArray Int a) -> Expr Int -> Expr a
readIArray arr i = ReadIArray arr i

arrayLength :: Storable a => Expr (UArray Int a) -> Expr Int
arrayLength arr = ArrayLength arr

printE :: (Computable a, Show (Internal a)) => a -> M ()
printE a = M (\k -> Print (internalize a) `Bind` (\_ -> k ()))

if_ :: Computable a => Expr Bool -> a -> a -> a
if_ e a b = externalize $ If e (internalize a) (internalize b)

iterateWhile :: Computable st => (st -> Expr Bool) -> (st -> st) -> st -> st
iterateWhile cond step init = externalize $ IterateWhile (lowerFun cond) (lowerFun step) (internalize init)

whileE :: Computable st => (st -> Expr Bool) -> (st -> st) -> (st -> M ()) -> st -> M () -- a :: Expr (Internal st), action :: st -> M (), internalize :: st -> Expr (Internal st)
whileE cond step action init = M (\k -> WhileM (lowerFun cond) (lowerFun step) (\a -> unM ((action . externalize) a) (\() -> Skip)) (internalize init)
                                        `Bind` (\_ -> k ()))

runMutableArray :: Storable a => M (Expr (IOUArray Int a)) -> Expr (UArray Int a)
runMutableArray m = RunMutableArray (runM m)


-- Eval

eval :: Expr a -> a
eval (Value a) = a

eval (Binop Plus  a b) = eval a + eval b
eval (Binop Minus a b) = eval a - eval b
eval (Binop Mult  a b) = eval a * eval b
eval (Binop Max a b) = max (eval a) (eval b)
eval (Binop Min a b) = min (eval a) (eval b)
eval (Binop And a b) = eval a && eval b
eval (Binop Or  a b) = eval a || eval b

eval (Abs a) = abs (eval a)
eval (Signum a) = signum (eval a)
eval (FromInteger t i) = fromInteger i

eval (Equal a b) = (eval a) == (eval b)
eval (NotEqual a b) = (eval a) /= (eval b)

eval (LTH a b) = (eval a) <  (eval b)
eval (LTE a b) = (eval a) <= (eval b)
eval (GTH a b) = (eval a) >  (eval b)
eval (GTE a b) = (eval a) >= (eval b)

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
showExpr i (FromInteger t n) = show n
showExpr i (FromRational t r) = "(fromRational " ++ (show r) ++ ")"
showExpr i (BoolLit b)     = show b
showExpr i (Equal a b)     = "(" ++ (showExpr i a) ++ " == " ++ (showExpr i b) ++ ")"
showExpr i (NotEqual a b)     = "(" ++ (showExpr i a) ++ " /= " ++ (showExpr i b) ++ ")"
showExpr i (LTH a b)     = "(" ++ (showExpr i a) ++ " < " ++ (showExpr i b) ++ ")"
showExpr i (LTE a b)     = "(" ++ (showExpr i a) ++ " <= " ++ (showExpr i b) ++ ")"
showExpr i (GTH a b)     = "(" ++ (showExpr i a) ++ " > " ++ (showExpr i b) ++ ")"
showExpr i (GTE a b)     = "(" ++ (showExpr i a) ++ " >= " ++ (showExpr i b) ++ ")"
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
showBinOp i Max a b     = "(max " ++ (showExpr i a) ++ " " ++ (showExpr i b) ++ ")"
showBinOp i Min a b     = "(min " ++ (showExpr i a) ++ " " ++ (showExpr i b) ++ ")"


translate :: Expr a -> Q Exp
translate (Var2 n) = return $ VarE n

translate (BoolLit b) = [| b |]

translate (Binop op a b) =
  case op of
       Plus   -> [| $(e1) + $(e2) |]
       Minus -> [| $(e1) - $(e2) |]
       Mult  -> [| $(e1) * $(e2) |]
       Max -> [| max $(translate a) $(translate b) |]
       Min -> [| min $(translate a) $(translate b) |]
  where e1 = translate a
        e2 = translate b
translate (Abs a) = [| abs $(translate a) |]
translate (Signum a) = [| signum $(translate a) |]
translate (FromInteger t n) = [| n |]

translate (Equal a b) = [| $(translate a) == $(translate b) |]
translate (NotEqual a b) = [| $(translate a) /= $(translate b) |]

translate (LTH a b) = [| $(translate a) <  $(translate b) |]
translate (LTE a b) = [| $(translate a) <= $(translate b) |]
translate (GTH a b) = [| $(translate a) >  $(translate b) |]
translate (GTE a b) = [| $(translate a) >= $(translate b) |]

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

newIOUArray :: Storable a => (Int, Int) -> IO (IOUArray Int a)
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

instance (Computable a, Computable b, Computable c) => Computable (a,b,c) where
  type Internal (a,b,c) =
    Cons (Internal a) (Cons (Internal b) (Ein (Internal c))) Id
  internalize (a,b,c) =
    TupN (internalize a ::. internalize b ::. Ein (internalize c))
  externalize t =
    (externalize (getN Z t), externalize (getN nat1 t), externalize (getN nat2 t))


instance (Computable a0, Computable a1, Computable a2,
          Computable a3, Computable a4, Computable a5,
          Computable a6, Computable a7, Computable a8) => Computable (a0,a1,a2,a3,a4,a5,a6,a7,a8) where
  type Internal (a0,a1,a2,a3,a4,a5,a6,a7,a8) =
     Cons (Internal a0) (Cons (Internal a1) (Cons (Internal a2)
    (Cons (Internal a3) (Cons (Internal a4) (Cons (Internal a5)
    (Cons (Internal a6) (Cons (Internal a7) (Ein  (Internal a8))))))))) Id
  internalize (a0,a1,a2,a3,a4,a5,a6,a7,a8) =
    TupN ((internalize a0) ::. (internalize a1) ::. (internalize a2) ::.
          (internalize a3) ::. (internalize a4) ::. (internalize a5) ::.
          (internalize a6) ::. (internalize a7) ::. (Ein (internalize a8)))
  externalize t =
    (externalize (getN Z    t), externalize (getN nat1 t),
     externalize (getN nat2 t), externalize (getN nat3 t),
     externalize (getN nat4 t), externalize (getN nat5 t),
     externalize (getN nat6 t), externalize (getN nat7 t),
     externalize (getN nat8 t))

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


