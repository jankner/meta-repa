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

import qualified Prelude as P
import Prelude (Num(..),Fractional(..),($),(.),Int,Bool,String,IO,Integral,Ord,Eq)
import Control.Monad

import Core
import HOAS hiding (Z)

infixr 8 ^^
infixr 8 ^
infixl 7 `div`
infixl 7 `mod`
infixl 7 `quot`
infixl 7 `rem`
infix  4 ==
infix  4 /=
infix  4 >=
infix  4 <=
infix  4 >
infix  4 <
infixr 3 &&
infixr 2 ||


(==) :: (Eq a, Typeable a) => Expr a -> Expr a -> Expr Bool
a == b = Equal typeOf0 a b

(/=) :: (Eq a, Typeable a) => Expr a -> Expr a -> Expr Bool
a /= b = NotEqual typeOf0 a b

(<) :: (Ord a, Typeable a) => Expr a -> Expr a -> Expr Bool
a < b = LTH typeOf0 a b

(>) :: (Ord a, Typeable a) => Expr a -> Expr a -> Expr Bool
a > b = GTH typeOf0 a b

(<=) :: (Ord a, Typeable a) => Expr a -> Expr a -> Expr Bool
a <= b = LTE typeOf0 a b

(>=) :: (Ord a, Typeable a) => Expr a -> Expr a -> Expr Bool
a >= b = GTE typeOf0 a b

max :: (Ord a, Typeable a) => Expr a -> Expr a -> Expr a
max = Binop typeOf0 Max

min :: (Ord a, Typeable a) => Expr a -> Expr a -> Expr a
min = Binop typeOf0 Min

(&&) :: Expr Bool -> Expr Bool -> Expr Bool
(&&) = Binop typeOf0 And

(||) :: Expr Bool -> Expr Bool -> Expr Bool
(||) = Binop typeOf0 Or

quot :: (Integral a, Typeable a) => Expr a -> Expr a -> Expr a
quot = Binop typeOf0 Quot

rem :: (Integral a, Typeable a) => Expr a -> Expr a -> Expr a
rem = Binop typeOf0 Rem

div :: (Integral a, Typeable a) => Expr a -> Expr a -> Expr a
div = Binop typeOf0 Div

mod :: (Integral a, Typeable a) => Expr a -> Expr a -> Expr a
mod = Binop typeOf0 Mod

true :: Expr Bool
true = BoolLit P.True

false :: Expr Bool
false = BoolLit P.False

fromIntegral :: (Integral a, Num b, Typeable b, Typeable a) => Expr a -> Expr b
fromIntegral = FromIntegral typeOf0 typeOf0

even :: (Storable a, Integral a) => Expr a -> Expr Bool
even a = a `rem` 2 == 0

odd a = a `rem` 2 == 1

(^) :: (Num a, Computable a, Integral b, Storable b) => a -> Expr b -> a
x0 ^ y0 =
  if_ (y0 == 0)
    1
    (let_
      loop1
      (\(x,y) ->
        if_ (y == 1)
        --then
          x
        --else
          (let_
            (loop2 x y)
            (\(x,y,z) -> x*z))))
  where loop1 =
            (iterateWhile (\(x,y) -> y /= 1 && even y) 
              (\(x,y) -> (x*x, y `quot` 2))
              (x0,y0))
        loop2 :: (Num a, Computable a, Integral b, Storable b) => a -> Expr b -> (a, Expr b, a)
        loop2 x y =
            (iterateWhile (\(x,y,z) -> y /= 1)
              (\(x,y,z) ->
                if_ (even y)
                --then
                  (x*x, y `quot` 2, z)
                --else
                  (x*x, (y-1) `quot` 2, z * x))
              (x*x, (y-1) `quot` 2, x))
            

(^^) :: (Fractional a, Computable a, Integral b, Storable b) => a -> Expr b -> a
x ^^ y = if_ (y <= 0)
          (x ^ y)
          (recip (x^(negate y)))

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
  toShape :: Int -> Expr (IArray Length) -> Shape sh

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

offset :: Shape sh -> Shape sh -> Shape sh
offset Z Z = Z
offset (sh1 :. n1) (sh2 :. n2) = offset sh1 sh2 :. (n1 + n2)

mapShape :: (Expr Int -> Expr Int) -> Shape sh -> Shape sh
mapShape f Z = Z
mapShape f (sh :. n) = mapShape f sh :. f n

zipShape :: (Expr Int -> Expr Int -> Expr Int) -> Shape sh -> Shape sh -> Shape sh
zipShape f Z Z = Z
zipShape f (sh1 :. n1) (sh2 :. n2) = zipShape f sh1 sh2 :. (n1 `f` n2)

forShape :: Shape sh -> (Expr Int -> M ()) -> M ()
forShape Z k = k 0
forShape sh k = parM (size sh) k

data Pull sh a = Pull (Shape sh -> a) (Shape sh)

instance P.Functor (Pull sh) where
  fmap f (Pull ixf sh) = Pull (f . ixf) sh

fromFunction :: (Shape sh -> a) -> Shape sh -> Pull sh a
fromFunction ixf sh = Pull ixf sh

storePull :: Storable a => Pull sh (Expr a) -> M (Expr (MArray a))
storePull (Pull ixf sh) = 
  do arr <- newArrayE (size sh)
     forShape sh (\i -> writeArrayE arr i (ixf (fromIndex sh i))) 
     P.return arr

traverse :: Pull sh a -> (Shape sh -> Shape sh') -> ((Shape sh -> a) -> Shape sh' -> b) -> Pull sh' b
traverse (Pull ixf sh) shFn elemFn = Pull (elemFn ixf) (shFn sh)


backpermute :: Shape sh2 -> (Shape sh2 -> Shape sh1) -> Pull sh1 a -> Pull sh2 a
backpermute sh2 perm (Pull ixf sh1) = Pull (ixf . perm) sh2


data Push sh a = Push ((Shape sh -> a -> M ()) -> M ()) (Shape sh)

instance P.Functor (Push sh) where
  fmap f (Push m sh) = Push m' sh
    where m' k = m (\i a -> k i (f a))


storePush :: Storable a => Push sh (Expr a) -> M (Expr (MArray a))
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

zipWith :: (Computable a, Computable b, Computable c) => (a -> b -> c) -> Pull sh a -> Pull sh b -> Pull sh c
zipWith f (Pull ixf1 sh1) (Pull ixf2 sh2) = Pull (\ix -> f (ixf1 ix) (ixf2 ix)) (intersectDim sh1 sh2)

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

foldAllS :: Computable a => (a -> a -> a) -> a -> Pull sh a -> a
foldAllS f z (Pull ixf sh) = P.snd $ 
  iterateWhile (\(i,_) -> i < (size sh)) 
    (\(i,x) -> (i+1, x `f` (ixf (fromIndex sh i))))
    (0,z)

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

