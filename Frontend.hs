{-# LANGUAGE GADTs, TypeOperators, FlexibleInstances, FlexibleContexts, UndecidableInstances #-}
module Frontend where

import Data.Array.IO hiding (inRange,index)
import Data.Array.MArray hiding (inRange,index)

import qualified Prelude as P
import Prelude ((*),(+),(-),($),(.),Int,Bool,String,IO,Integral,Ord,Eq)
import Control.Monad

import Repa

infix  4 ==
infix  4 /=
infix  4 >=
infix  4 <=
infix  4 >
infix  4 <
infixr 3 &&
infixr 2 ||


(==) :: Eq a => Expr a -> Expr a -> Expr Bool
a == b = Equal a b

(/=) :: Eq a => Expr a -> Expr a -> Expr Bool
a /= b = NotEqual a b

(<) :: Ord a => Expr a -> Expr a -> Expr Bool
a < b = LTH a b

(>) :: Ord a => Expr a -> Expr a -> Expr Bool
a > b = GTH a b

(<=) :: Ord a => Expr a -> Expr a -> Expr Bool
a <= b = LTE a b

(>=) :: Ord a => Expr a -> Expr a -> Expr Bool
a >= b = GTE a b

max :: Ord a => Expr a -> Expr a -> Expr a
max = Max

min :: Ord a => Expr a -> Expr a -> Expr a
min = Min

(&&) :: Expr Bool -> Expr Bool -> Expr Bool
a && b = And a b

(||) :: Expr Bool -> Expr Bool -> Expr Bool
a || b = Or a b

quot :: Integral a => Expr a -> Expr a -> Expr a
quot = Quot

rem :: Integral a => Expr a -> Expr a -> Expr a
rem = Rem

true :: Expr Bool
true = BoolLit P.True

false :: Expr Bool
false = BoolLit P.False



type Index  = P.Int
type Length = P.Int

data Z
data tail :. head

infixl 3 :.

data Shape sh where
  Z    :: Shape Z
  (:.) :: Shape sh -> Expr Length -> Shape (sh :. Expr Length)


type DIM0 = Z
type DIM1 = DIM0 :. Expr Length
type DIM2 = DIM1 :. Expr Length
type DIM3 = DIM2 :. Expr Length


dim :: Shape sh -> Int
dim Z = 0
dim (sh :. _) = dim sh + 1

{-
class Shapely sh where
  mkShape :: Expr Index -> Shape sh
  toShape :: Int -> Expr [Length] -> Shape sh

instance Shapely Z where
  mkShape _ = Z
  toShape _ _ = Z

instance Shapely sh => Shapely (sh :. Expr Length) where
  mkShape i = mkShape i :. i
  toShape i arr
      = toShape (i+1) arr :. (arr ! (P.fromIntegral i))

zeroDim :: Shapely sh => Shape sh
zeroDim = mkShape 0

unitDim :: Shapely sh => Shape sh
unitDim = mkShape 1

fakeShape :: Shapely sh => String -> Shape sh
fakeShape err = mkShape (P.error err)
-}

size :: Shape sh -> Expr Length
size Z         = 1
size (sh :. l) = size sh * l

toIndex :: Shape sh -> Shape sh -> Expr Index
toIndex Z _ = 0
toIndex (sh1 :. sh2) (i1 :. i2) = toIndex sh1 i1 * sh2 + i2

fromIndex :: Shape sh -> Expr Index -> Shape sh
fromIndex Z _ = Z
fromIndex sh@(_ :. _) i = fromIndexOne sh i

fromIndexOne :: Shape (sh :. Expr Index) -> Expr Index -> Shape (sh :. Expr Index)
fromIndexOne (Z :. _) ix = Z :. ix
fromIndexOne (ds@(_ :. _) :. d) ix = fromIndexOne ds (ix `quot` d) :. (ix `rem` d)

intersectDim :: Shape sh -> Shape sh -> Shape sh
intersectDim Z Z = Z
intersectDim (sh1 :. n1) (sh2 :. n2) = (intersectDim sh1 sh2 :. (min n1 n2))

inRange :: Shape sh -> Shape sh -> Shape sh -> Expr Bool
inRange Z Z Z = true
inRange (shL :. l) (shU :. u) (sh :. i) = l <= i && i < u && inRange shL shU sh

toList :: Shape sh -> [Expr Length]
toList Z = []
toList (sh :. i) = i : toList sh

forShape :: Shape sh -> (Shape sh -> M ()) -> M ()
forShape Z k = k Z
forShape (sh :. l) k = forShape sh (\sh2 -> parM l (\i -> k (sh2 :. i)))

data Pull sh a = Pull (Shape sh -> a) (Shape sh)

instance P.Functor (Pull sh) where
  fmap f (Pull ixf sh) = Pull (f . ixf) sh

fromFunction :: (Shape sh -> a) -> Shape sh -> Pull sh a
fromFunction ixf sh = Pull ixf sh

storePull :: MArray IOUArray a IO => Pull sh (Expr a) -> M (Expr (IOUArray Length a))
storePull (Pull ixf sh) = 
  do arr <- newArrayE (size sh)
     forShape sh (\i -> writeArrayE arr (toIndex sh i) (ixf i)) 
     P.return arr

traverse :: Pull sh a -> (Shape sh -> Shape sh') -> ((Shape sh -> a) -> Shape sh' -> b) -> Pull sh' b
traverse (Pull ixf sh) shFn elemFn = Pull (elemFn ixf) (shFn sh)


backpermute :: Shape sh2 -> (Shape sh2 -> Shape sh1) -> Pull sh1 a -> Pull sh2 a
backpermute sh2 perm (Pull ixf sh1) = Pull (ixf . perm) sh2


data Push sh a = Push ((Shape sh -> a -> M ()) -> M ()) (Shape sh)


storePush :: MArray IOUArray a IO => Push sh (Expr a) -> M (Expr (IOUArray Length a))
storePush (Push m sh) =
  do arr <- newArrayE (size sh)
     m (\i a -> writeArrayE arr (toIndex sh i) a)
     P.return arr

(+.+) :: Push (sh:.Expr Length) a -> Push (sh:.Expr Length) a -> Push (sh:.Expr Length) a
(Push m1 (sh1:.l1)) +.+ (Push m2 (sh2:.l2)) = Push m (sh1:.(l1 + l2))
  where m k = m1 k >> m2 (\(sh:.i) a -> k (sh:.(i+l1)) a)

permute :: Shape sh2 -> (Shape sh1 -> Shape sh2) -> Push sh1 a -> Push sh2 a
permute sh2 perm (Push m sh1) = Push (\k -> m (\i a -> k (perm i) a)) sh2


class Arr arr where
  toPush :: arr sh a -> Push sh a
  ixMap  :: (Shape sh -> Shape sh) -> arr sh a -> arr sh a
  extent :: arr sh a -> (Shape sh)

instance Arr Pull where
  toPush (Pull ixf sh) = Push m sh
    where m k = forShape sh (\i -> k i (ixf i))
  ixMap f (Pull ixf sh) = Pull (ixf . f) sh
  extent (Pull _ sh) = sh

instance Arr Push where
  toPush = P.id
  ixMap f (Push m sh) = permute sh f (Push m sh)
  extent (Push _ sh) = sh

index :: Pull sh a -> Shape sh -> a
index (Pull ixf s) = ixf

foldS :: (Computable b, Computable a) => b -> (a -> b -> b) -> Pull (sh :. Expr Length) a -> Pull sh b
foldS s f (Pull ixf (sh :. n)) = fromFunction (\sh -> P.snd $ iterateWhile (\(i,_) -> i < n) (\(i,s) -> (i+1, ixf (sh :. i) `f` s)) (0, s)) sh

sumS :: (P.Num a, Computable a) => Pull (sh :. Expr Length) a -> Pull sh a
sumS = foldS 0 (+)
