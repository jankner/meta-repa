{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
module Eval where

import System.IO.Unsafe

import Data.Vector.Unboxed
import Data.Vector.Unboxed.Mutable

import Data.Array.Repa.Index
import Data.Array.Repa.Eval.Gang

import Data.Int

import GHC.Exts
import Prelude		as P


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

runMutableArray :: (Unbox a) => IO (IOVector a) -> Vector a
runMutableArray arr = unsafePerformIO (arr >>= unsafeFreeze)

newIOUArray :: (Unbox a) => Int -> IO (IOVector a)
newIOUArray = new

