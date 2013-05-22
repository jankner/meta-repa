{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Eval where

import System.IO.Unsafe

import Data.Array.IO hiding (unsafeFreeze)
import Data.Array.MArray hiding (unsafeFreeze)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.Unsafe

import Data.Array.Repa.Index
import Data.Array.Repa.Eval.Gang

import Data.Int
import Data.Word

import GHC.Exts
import Prelude		as P

import Control.DeepSeq

import MaybeNF
import GenInstance

instance MaybeNF (a -> b) where
  maybeDeepSeq = flip const

instance MaybeNF (UArray Int a) where
  maybeDeepSeq = seq

instance MaybeNF (IOUArray Int a) where
  maybeDeepSeq = seq

instance MaybeNF (IO a) where
  maybeDeepSeq = flip const --seq

instance MaybeNF Bool where
  maybeDeepSeq = seq

instance MaybeNF Int where
  maybeDeepSeq = seq

instance MaybeNF Word where
  maybeDeepSeq = seq

instance MaybeNF Int64 where
  maybeDeepSeq = seq

instance MaybeNF Word64 where
  maybeDeepSeq = seq

instance MaybeNF Float where
  maybeDeepSeq = seq

instance MaybeNF Double where
  maybeDeepSeq = seq

instance MaybeNF () where
  maybeDeepSeq = seq

deriveMaybeNFTups 36

{-
instance (MaybeNF a, MaybeNF b) => MaybeNF (a, b) where
  maybeDeepSeq (a,b) x = a `maybeDeepSeq` b `maybeDeepSeq` x

instance (MaybeNF a, MaybeNF b, MaybeNF c) => MaybeNF (a, b, c) where
  maybeDeepSeq (a,b,c) x = a `maybeDeepSeq` b `maybeDeepSeq` c `maybeDeepSeq` x

instance (MaybeNF a, MaybeNF b, MaybeNF c,
          MaybeNF d, MaybeNF e, MaybeNF f,
          MaybeNF g, MaybeNF h, MaybeNF i) =>
    MaybeNF (a, b, c, d, e, f, g, h, i) where
 maybeDeepSeq (a, b, c, d, e, f, g, h, i) x =
  a `maybeDeepSeq` b `maybeDeepSeq` c `maybeDeepSeq`
  d `maybeDeepSeq` e `maybeDeepSeq` f `maybeDeepSeq`
  g `maybeDeepSeq` h `maybeDeepSeq` i `maybeDeepSeq` x
-}

while cond step init = loop init
  where loop s | cond s = loop (step s)
               | True   = s
{-# INLINE [0] while #-}

whileM :: Monad m => (a -> Bool) -> (a -> a) -> (a -> m ()) ->  a -> m ()
whileM cond step action init
  = let loop !s | cond s = action s >> loop (step s)
                | True   = P.return ()
    in loop init
{-# INLINE [0] whileM #-}

parM :: Int -> (Int -> IO ()) -> IO ()
parM (I# n) action = gangIO theGang $
  \(I# thread) ->
    let !start   = splitIx thread
        !end     = splitIx (thread +# 1#)
    in  run start end
  where !(I# threads)  = gangSize theGang
        !chunkLen 	   = n `quotInt#` threads
        !chunkLeftover = n `remInt#`  threads
                                                                  
        {-# INLINE splitIx #-}
        splitIx thread
          | thread <# chunkLeftover = thread *# (chunkLen +# 1#)
          | otherwise               = thread *# chunkLen  +# chunkLeftover
        
        {-# INLINE run #-}
        run !ix !end | ix >=# end = return ()
                     | otherwise  =
          do action (I# ix)
             run (ix +# 1#) end
{-# INLINE [0] parM #-}

runMutableArray :: (MArray IOUArray a IO, IArray UArray a) => IO (IOUArray Int a) -> UArray Int a
runMutableArray arr = unsafePerformIO (arr >>= unsafeFreeze)

newIOUArray :: (MArray IOUArray a IO) => (Int, Int) -> IO (IOUArray Int a)
newIOUArray = newArray_

