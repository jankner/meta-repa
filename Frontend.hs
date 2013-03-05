{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
module Frontend where

import Data.Array.IO hiding (inRange,index)
import Data.Array.MArray hiding (inRange,index)
import Data.Array.IArray hiding (inRange,index)
import Data.Array.Unboxed hiding (inRange,index)

import qualified Prelude as P
import Prelude (Num(..),($),(.),Int,Bool,String,IO,Integral,Ord,Eq)
import Control.Monad

import Core
import HOAS hiding (Z)

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
max = Binop Max

min :: Ord a => Expr a -> Expr a -> Expr a
min = Binop Min

(&&) :: Expr Bool -> Expr Bool -> Expr Bool
(&&) = Binop And

(||) :: Expr Bool -> Expr Bool -> Expr Bool
(||) = Binop Or

quot :: Integral a => Expr a -> Expr a -> Expr a
quot = Binop Quot

rem :: Integral a => Expr a -> Expr a -> Expr a
rem = Binop Rem

true :: Expr Bool
true = BoolLit P.True

false :: Expr Bool
false = BoolLit P.False

fromIntegral :: (Integral a, Num b, Typeable b) => Expr a -> Expr b
fromIntegral = FromIntegral typeOf0


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


class Shapely sh where
  mkShape :: Expr Index -> Shape sh
  toShape :: Int -> Expr (UArray Int Length) -> Shape sh

instance Shapely Z where
  mkShape _ = Z
  toShape _ _ = Z

instance Shapely sh => Shapely (sh :. Expr Length) where
  mkShape i = mkShape i :. i
  toShape i arr
      = toShape (i+1) arr :. (readIArray arr (P.fromIntegral i))

zeroDim :: Shapely sh => Shape sh
zeroDim = mkShape 0

unitDim :: Shapely sh => Shape sh
unitDim = mkShape 1

fakeShape :: Shapely sh => String -> Shape sh
fakeShape err = mkShape (P.error err)


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

forShape :: Shape sh -> (Expr Int -> M ()) -> M ()
forShape Z k = k 0
forShape sh k = parM (size sh) k

data Pull sh a = Pull (Shape sh -> a) (Shape sh)

instance P.Functor (Pull sh) where
  fmap f (Pull ixf sh) = Pull (f . ixf) sh

fromFunction :: (Shape sh -> a) -> Shape sh -> Pull sh a
fromFunction ixf sh = Pull ixf sh

storePull :: Storable a => Pull sh (Expr a) -> M (Expr (IOUArray Length a))
storePull (Pull ixf sh) = 
  do arr <- newArrayE (size sh)
     forShape sh (\i -> writeArrayE arr i (ixf (fromIndex sh i))) 
     P.return arr

traverse :: Pull sh a -> (Shape sh -> Shape sh') -> ((Shape sh -> a) -> Shape sh' -> b) -> Pull sh' b
traverse (Pull ixf sh) shFn elemFn = Pull (elemFn ixf) (shFn sh)


backpermute :: Shape sh2 -> (Shape sh2 -> Shape sh1) -> Pull sh1 a -> Pull sh2 a
backpermute sh2 perm (Pull ixf sh1) = Pull (ixf . perm) sh2


data Push sh a = Push ((Shape sh -> a -> M ()) -> M ()) (Shape sh)


storePush :: Storable a => Push sh (Expr a) -> M (Expr (IOUArray Length a))
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
    where m k = forShape sh (\i -> let ish = fromIndex sh i
                                   in  k ish (ixf ish))
  ixMap f (Pull ixf sh) = Pull (ixf . f) sh
  extent (Pull _ sh) = sh

instance Arr Push where
  toPush = P.id
  ixMap f (Push m sh) = permute sh f (Push m sh)
  extent (Push _ sh) = sh

index :: Pull sh a -> Shape sh -> a
index (Pull ixf s) = ixf

scanS :: (Computable a, Computable b) => (a -> b -> a) -> a -> Pull (sh :. Expr Length) b -> Push (sh:.Expr Length) a
scanS f z (Pull ixf (sh:.n)) = Push m (sh:.n+1)
  where m k = forShape sh $ \i -> let ish = fromIndex sh i in
                whileE (\(i,_) -> i < (n+1)) 
                  (\(i,x) -> (i+1, x `f` (ixf (ish :. i))))
                  (\(i,x) -> k (ish :. i) x)
                  (0,z)

foldS :: (Computable b, Computable a) => b -> (a -> b -> b) -> Pull (sh :. Expr Length) a -> Pull sh b
foldS s f (Pull ixf (sh :. n)) = fromFunction (\sh -> P.snd $ iterateWhile (\(i,_) -> i < n) (\(i,s) -> (i+1, ixf (sh :. i) `f` s)) (0, s)) sh

sumS :: (P.Num a, Computable a) => Pull (sh :. Expr Length) a -> Pull sh a
sumS = foldS 0 (+)

interleave2 :: Push sh a -> Push sh a -> Push sh a
interleave2 (Push m1 (sh1 :. l1)) (Push m2 (sh2 :. l2)) = Push m (sh1 :. (l1 + l2))
  where m k = m1 (everyNPlusM 2 0 k) >> m2 (everyNPlusM 2 1 k)

interleave3 :: Push sh a -> Push sh a -> Push sh a -> Push sh a
interleave3 (Push m1 (sh1 :. l1)) (Push m2 (sh2 :. l2)) (Push m3 (sh3 :. l3)) = Push m (sh1 :. (l1 + l2 + l3))
  where m k = m1 (everyNPlusM 3 0 k) >> m2 (everyNPlusM 3 1 k) >> m3 (everyNPlusM 3 2 k)

everyNPlusM :: Expr Int -> Expr Int -> (Shape (sh :. Expr Int) -> a -> M ()) -> Shape (sh :. Expr Int) -> a -> M ()
everyNPlusM n m k (sh :. i) = k (sh :. (i * n + m))


interleave2' :: Pull (sh :. Expr Int) a -> Pull (sh :. Expr Int) a -> Push (sh :. Expr Int) a
interleave2' (Pull ixf1 (sh1 :. l1)) (Pull ixf2 (sh2 :. l2)) = Push m sh
  where m k = forShape (sh1:.l1) (\i -> case fromIndex (sh1:.l1) i of 
                s@(sh :. i) ->
                  k (sh :. (i * 2)) (ixf1 s) >>
                  k (sh :. (i * 2 + 1)) (ixf2 s))
        sh  = sh1 :. (l1 + l2)


reverse :: (Selector sel sh, Arr arr) => sel -> arr sh a -> arr sh a
reverse sel arr = ixMap (adjustLength sel (n-)) arr
  where n = selectLength sel (extent arr)


conc :: (Selector sel sh) => sel -> Push sh a -> Push sh a -> Push sh a
conc sel (Push m1 sh1) (Push m2 sh2) = Push m (adjustLength sel (+ selectLength sel sh2) sh1)
  where m k = m1 k >>
              m2 (\sh a -> k (adjustLength sel (+ selectLength sel sh1) sh) a)


force :: Storable a => Push sh (Expr a) -> Push sh (Expr a)
force (Push f l) = Push f' l
  where f' k = do arr <- newArrayE (size l)
                  f (\sh a -> writeArrayE arr (toIndex l sh) a)
                  forShape l $ \i -> do
                    a <- readArrayE arr i
                    k (fromIndex l i) a


forcePull :: Storable a => Pull sh (Expr a) -> Pull sh (Expr a)
forcePull p@(Pull ixf sh) = Pull (\ix -> ixf' arr ix) sh
  where ixf' arr ix = readIArray arr (toIndex sh ix)
        arr = runMutableArray (storePull p)


data This = This
data NotThis = NotThis

data Z' = Z'

data tail :.: head = tail :.: head

class Selector sel sh | sel -> sh where
  selectLength :: sel -> Shape sh -> Expr Length
  adjustLength :: sel -> (Expr Length -> Expr Length) -> Shape sh -> Shape sh

instance Selector This (sh :. Expr Length) where
  selectLength This (_ :. l) = l
  adjustLength This f (sh :. l) = sh :. (f l)

instance Selector sel sh => Selector (sel :.: NotThis) (sh :. Expr Length) where
  selectLength (sel :.: NotThis) (sh :. _) = selectLength sel sh
  adjustLength (sel :.: NotThis) f (sh :. l) = (adjustLength sel f sh) :. l


data All = All
data Any sh = Any

type family FullShape ss
type instance FullShape Z'                   = Z
type instance FullShape (Any sh)             = sh
type instance FullShape (sl :.: Expr Length) = FullShape sl :. Expr Length
type instance FullShape (sl :.: All)         = FullShape sl :. Expr Length

type family SliceShape ss
type instance SliceShape Z'                   = Z
type instance SliceShape (Any sh)             = sh
type instance SliceShape (sl :.: Expr Length) = SliceShape sl
type instance SliceShape (sl :.: All)         = SliceShape sl :. Expr Length


class Slice ss where
  sliceOfFull :: ss -> Shape (FullShape ss) -> Shape (SliceShape ss)
  fullOfSlice :: ss -> Shape (SliceShape ss) -> Shape (FullShape ss)

instance Slice Z' where
  sliceOfFull Z' Z = Z
  fullOfSlice Z' Z = Z

instance Slice (Any sh) where
  sliceOfFull Any sh = sh
  fullOfSlice Any sh = sh

instance Slice sl => Slice (sl :.: Expr Length) where
  sliceOfFull (sl :.: _) (sh :. _) = sliceOfFull sl sh
  fullOfSlice (sl :.: n) sh        = fullOfSlice sl sh :. n

instance Slice sl => Slice (sl :.: All) where
  sliceOfFull (sl :.: All) (sh :. s) = sliceOfFull sl sh :. s
  fullOfSlice (sl :.: All) (sh :. s) = fullOfSlice sl sh :. s


-- | Duplicates part of a vector along a new dimension.
replicate :: Slice sl
          => sl -> Pull (SliceShape sl) a
          -> Pull (FullShape  sl) a
replicate sl vec
 = backpermute (fullOfSlice sl (extent vec))
               (sliceOfFull sl) vec

-- | Extracts a slice from a vector.
slice :: Slice sl
      => Pull (FullShape sl) a
      -> sl -> Pull (SliceShape sl) a
slice vec sl
 = backpermute (sliceOfFull sl (extent vec))
               (fullOfSlice sl) vec

