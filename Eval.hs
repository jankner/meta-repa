{-# LANGUAGE TemplateHaskell #-}
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


while cond step init = loop init
  where loop s | cond s = loop (step s)
               | True   = s
{-# INLINE [0] while #-}

rec :: ((a -> r) -> a -> r) -> a -> r
rec f x = let recf x = f recf x
          in recf x
{-# INLINE rec #-}

whileM :: Monad m => (a -> Bool) -> (a -> a) -> (a -> m ()) ->  a -> m ()
whileM cond step action init
  = let loop !s | cond s = action s >> loop (step s)
                | True   = P.return ()
    in loop init
{-# INLINE [0] whileM #-}

parM :: Int# -> (Int# -> IO ()) -> IO ()
parM n action = gangIO theGang $
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
          do action ix
             run (ix +# 1#) end
{-# INLINE [0] parM #-}

runMutableArray :: (MArray IOUArray a IO, IArray UArray a) => IO (IOUArray Int a) -> UArray Int a
runMutableArray arr = unsafePerformIO (arr >>= unsafeFreeze)

newIOUArray :: (MArray IOUArray a IO) => (Int, Int) -> IO (IOUArray Int a)
newIOUArray = newArray_

