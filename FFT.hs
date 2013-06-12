{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module FFT where

import qualified Prelude as P
import Prelude (Eq,Num(..),Fractional(..),Floating(..),Real(..),
                ($),(.),flip,(>>),Int,Monad(..),Bool,Double)
import Frontend
import HOAS hiding (Z)

import Data.Bits (Bits)
import qualified Data.Bits as B

-- | DFT2 for Decimation-In-Frequency
dft2 :: Num a => a -> a -> a -> (a,a)
dft2 w x0 x1 = (x0+x1, (x0-x1)*w)

butterfly :: (Computable a, Num a) => Pull DIM1 a -> Pull DIM1 a -> Push DIM1 a
butterfly ws vs = unhalve $ zipWith3 dft2 ws ys zs
  where
    (ys,zs) = halve vs

runFFT vs = fft (twids (length1 vs)) vs

-- | Cooley-Tukey Radix-2 Decimation In Frequency Fast Fourier Transfrom
--
-- >>> eval (fft (twids 8)) [1,1,1,1,0,0,0,0]
-- [4.0 :+ 0.0,0.0 :+ 0.0,0.0 :+ 0.0,0.0 :+ 0.0,1.0 :+ (-2.414213562373095),0.9999999999999999 :+ 0.4142135623730949,1.0 :+ (-0.4142135623730949),0.9999999999999997 :+ 2.414213562373095]
--
fft :: (Computable a, Num a, Storable (Internal a)) => Pull DIM1 a -> Pull DIM1 a -> Pull DIM1 a
fft ws vs = fromMem (extent vs) $ forLoop (ilog2 $ length1 vs) (toMem $ toPush vs) stage
  where
    stage s xs = toMem $ chnk (arrayLength xs .>>. s) (butterfly (ixMap (ixMap1 (.<<. s)) ws)) $ fromMem (extent vs) xs

twid :: Expr Length -> Expr Index -> Complex Double
twid n k = cis (-2 * pi * i2f k / i2f n)

twids :: Expr Length -> Pull DIM1 (Complex Double)
twids n = fromFunction (\(Z :. k) -> twid n k) (Z :. n `div` 2)
{-
bitRev :: Pull DIM1 a -> Pull DIM1 a
bitRev xs = composeOn (\ix a -> ixMap (ixMap1 (rotBit ix)) a) (1 ... n) xs
  where n = ilog2 (length1 xs) - 1
-}
-- | Utilities that should go into Feldspar.Core.Frontend.Bits

tstBit :: (Num a, Bits a, Storable a) => Expr a -> Expr Index -> Expr Bool
tstBit w b = w .&. bit b /= 0

setbit :: (Bits a, Typeable a) => Expr a -> Expr Index -> Expr a
setbit w b = w .|. bit b

clrbit :: (Bits a, Typeable a) => Expr a -> Expr Index -> Expr a
clrbit w b = w .&. complement (bit b)

iZero :: (Num a, Bits a, Storable a) => Expr Index -> Expr a -> Expr a
iZero b w = w + (w .&. complement (oneBits b))

iOne :: (Num a, Bits a, Storable a) => Expr Index -> Expr a -> Expr a
iOne b w = bit b `xor` iZero b w

type Pull1 a = Pull (Shape (Z :. Expr Length)) (Expr a)
type Push1 a = Push (Shape (Z :. Expr Length)) (Expr a)

i2f i = fromIntegral i

rotBit a i = rotate a i

forLoop :: Computable s => Expr Int -> s -> (Expr Int -> s -> s) -> s
forLoop i s body = P.snd $ iterateWhile ((< i) . P.fst) (\(i,s) -> (i+1,body i s)) (0,s)

oneBits :: (Num a, Bits a, Storable a) => Expr Index -> Expr a
oneBits n = complement (allOnes .<<. n)

allOnes :: (Num a, Bits a, Storable a) => Expr a
allOnes = complement 0

-- | QuickCheck
{-
fft' xs = eval (bitRev . fft (twids len)) xs
  where len = value $ P.fromIntegral $ P.length xs

prop_is_fft f g = forAll (suchThat arbitrary (btw 2 10)) $ \l ->
    let len = Expr.Bits.shiftL 1 (P.fromIntegral (l::Word))
    in forAll (vectorOf len arbitrary) $ \xs ->
      P.and $ P.zipWith (eqComplex 1e-4) (f xs) (g xs)

eqComplex tol (a:+ai) (b:+bi) = P.and [ tol P.> P.abs (a - b)
                                      , tol P.> P.abs (ai - bi)
                                      ]

btw :: P.Ord a => a -> a -> a -> Bool
btw l h a = a P.> l P.&& a P.< h
-}


-- | Utilities that should go into Feldspar.Vector.Push

chnk :: (Arr arr1, Computable b)
      => Expr Length            -- ^ Size of the chunks
      -> (Pull DIM1 a -> arr1 DIM1 b) -- ^ Applied to every chunk
      -> Pull DIM1 a
      -> Push DIM1 b
chnk c f v = Push loop (Z :. noc * c)
  where l = length1 v
        noc = l `div` c
        loop func = parM noc $ \i ->
                      do let (Push k _) = toPush $ f (take c (drop (c*i) v))
                         k (\(Z :. j) a -> func (Z :. (c*i + j)) a)

unpairWith :: (Arr arr, Computable a)
           => ((Shape (Z :. Expr Index) -> a -> M ()) -> Shape (Z :. Expr Index) -> (a,a) -> M ())
           -> arr DIM1 (a,a) -> Push DIM1 a
unpairWith spread arr = case toPush arr of
                          Push f (Z :. l) -> Push (f . spread) (Z :. 2*l)

fromDIM1 :: (Shape (Z :. Expr Index) -> a) -> (Expr Index -> a)
fromDIM1 f i = f (Z :. i)

toDIM1 :: (Expr Index -> a) -> (Shape (Z :. Expr Index) -> a)
toDIM1 f (Z :. i) = f i

ixMap1 :: (Expr Index -> Expr Index) -> (Shape (Z :. Expr Index) -> Shape (Z :. Expr Index))
ixMap1 f (Z :. ix) = Z :. f ix

-- unpair = unpairWith everyOther

-- everyOther = stride 2 1

unhalve :: (Arr arr, Computable a)
        => arr DIM1 (a,a) -> Push DIM1 a
unhalve xs = unpairWith (stride 1 (length xs)) xs

stride :: Expr Length -> Expr Length
       -> (Shape (Z :. Expr Index) -> a -> M b)
       -> Shape (Z :. Expr Index) -> (a,a) -> M b
stride n k f (Z :. ix) (a1,a2) = f (Z :. (n*ix)) a1 >> f (Z :. (n*ix+k)) a2

length :: Arr arr => arr (Z :. Expr Int) a -> Expr Int
length arr = case extent arr of
               (Z :. l) -> l


-- ex v = {- bitRev $-} fft (twids $ length1 v) v

dim1 :: (Expr Index -> a) -> (Shape (Z :. Expr Index) -> a)
dim1 f (Z :. l) = f l

-- Things which could be added to meta-repa

zipWith3 :: (Computable a, Computable b, Computable c, Computable d) => (a -> b -> c -> d) -> Pull sh a -> Pull sh b -> Pull sh c -> Pull sh d
zipWith3 f (Pull ixf1 sh1) (Pull ixf2 sh2) (Pull ixf3 sh3) = Pull (\ix -> f (ixf1 ix) (ixf2 ix) (ixf3 ix)) (intersectDim (intersectDim sh1 sh2) sh3)

halve :: Pull DIM1 a ->
        (Pull DIM1 a, Pull DIM1 a)
halve (Pull ixf (Z :. l)) = (Pull ixf (Z :. (l `div` 2)),
                             Pull (\(Z :. ix) -> ixf (Z :. ix + (l `div` 2))) (Z :. ((l+1) `div` 2)))

take :: Expr Int -> Pull DIM1 a -> Pull DIM1 a
take i (Pull ixf (Z :. l)) = Pull ixf (Z :. (min i l))

drop :: Expr Int -> Pull DIM1 a -> Pull DIM1 a
drop i (Pull ixf (Z :. l)) = Pull (\(Z :. ix) -> ixf (Z :. ix + l)) (Z :. max (l - i) 0)

(...) :: Expr Int -> Expr Int -> Pull DIM1 (Expr Int)
f ... t = Pull (\ (Z :. i) -> i + f) (Z :. t - f + 1)

freezeToVector :: Storable a => Push sh (Expr a) -> Pull sh (Expr a)
freezeToVector (Push loop sh) = Pull (ixf arr) sh
  where ixf arr ix = readIArray arr (toIndex sh ix)
        arr = runMutableArray $
              do arr' <- newArrayE (size sh)
                 loop (\l a ->
                        writeArrayE arr' (toIndex sh l) a)
                   
                 return arr'                   
{-
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
-}

composeOn :: (Computable a) => (b -> a -> a) -> Pull DIM1 b -> a -> a
composeOn = flip . fold . flip

type Complex a = (Expr a, Expr a)

instance (Eq a,Num a,Floating a, Storable a) => Num (Expr a, Expr a) where
  (a1,b1) + (a2,b2) = (a1+a2,b1+b2)
  (a1,b1) * (a2,b2) = (a1*a2-b1*b2,a1*b2+b1*a2)
  negate (a,b)      = (negate a, negate b)
  fromInteger n     = (fromInteger n,0)
  abs z             = (magnitude z,0)
  signum z@(x,y)   = if_ (x == 0 && y == 0) (0,0) (x/r,y/r)
    where r = magnitude z

magnitude :: (Floating a, Storable a) => Complex a -> Expr a
magnitude (x,y) = sqrt (x*x + y*y)

cis :: (Storable a,Num a, Real a, Floating a) => Expr a -> Complex a
cis a = (cos a, sin a)

ilog2 :: (Typeable a,Bits a) => Expr a -> Expr Index
ilog2 x = bitSize x - 1 - nlz x

-- | Count leading zeros
--   Based on an algorithm in Hacker's Delight
nlz :: (Typeable a, Bits a) => Expr a -> Expr Index
nlz x = bitCount $ complement $ P.foldl go x $ P.takeWhile (P.< bitSize' x) $ P.map (2 P.^) [(0::P.Integer)..]

go :: (Typeable a, Bits a) => Expr a -> Index -> Expr a
go b s = b .|. (b .>>. P.fromIntegral s)

{-
fold :: (Computable a) =>
        (a -> a -> a)
     -> a
     -> Pull (sh :. Expr Length) a
     -> Pull sh a
fold f x vec = case extent vec of
                sh :. n -> Pull ixf sh
                  where ixf i = forLoop n x (\ix s -> f s (index vec (i :. ix)))
-}

fold :: Computable a => (a -> b -> a)
        -> a
        -> Pull (Z :. Expr Length) b
        -> a
fold f x vec = case extent vec of
                 Z :. n -> forLoop n x (\ix s -> f s (index vec (Z :. ix)))


bitSize :: forall a. Bits a => Expr a -> Expr Int
bitSize = P.const $ P.fromIntegral $ B.bitSize (P.undefined :: a)

bitSize' :: forall a. Bits a => Expr a -> Index
bitSize' = P.const $ B.bitSize (P.undefined :: a)

bitCount x = popCount x

length1 :: Pull (Z :. Expr Length) a -> Expr Length
length1 (Pull _ixf (Z :. l)) = l

toMem :: (Computable a, Storable (Internal a)) => Push sh a -> Expr (IArray (Internal a))
toMem (Push f sh) = runMutableArray $ do
                      arr <- newArrayE l
                      f (\ix a -> writeArrayE arr (toIndex sh ix) (internalize a))
                      return arr
  where
    l = size sh

fromMem :: (Computable a, Storable (Internal a)) => Shape sh -> Expr (IArray (Internal a)) -> Pull sh a
fromMem sh e = Pull ixf sh
  where ixf i = externalize $ readIArray e (toIndex sh i)

--type Complex a = (Expr a, Expr a)
