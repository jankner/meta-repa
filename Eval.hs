{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
module Eval where

import System.IO.Unsafe

import Data.Array.IO hiding (unsafeFreeze)
import Data.Array.MArray hiding (unsafeFreeze)
import Data.Array.IArray
import Data.Array.Unboxed
import Data.Array.Unsafe

import Data.Array.Repa.Index
import Data.Array.Repa.Eval.Gang

import GHC.Exts
import Prelude		as P


while cond step s | cond s    = while cond step (step s)
                  | otherwise = s

whileM :: Monad m => (a -> Bool) -> (a -> a) -> (a -> m ()) ->  a -> m ()
whileM cond step action s | cond s    = action s >> whileM cond step action (step s)
                          | otherwise = P.return ()


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

runMutableArray :: (MArray IOUArray a IO, IArray UArray a) => IO (IOUArray Int a) -> UArray Int a
runMutableArray arr = unsafePerformIO (arr >>= unsafeFreeze)

newIOUArray :: (MArray IOUArray a IO) => (Int, Int) -> IO (IOUArray Int a)
newIOUArray = newArray_

