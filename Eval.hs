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

infixr 0 `maybeDeepSeq`

class MaybeNF a where
  maybeDeepSeq :: a -> b -> b

instance MaybeNF (a -> b) where
  maybeDeepSeq = seq

instance MaybeNF (UArray Int a) where
  maybeDeepSeq = seq

instance MaybeNF (IOUArray Int a) where
  maybeDeepSeq = seq

instance MaybeNF (IO a) where
  maybeDeepSeq = seq

instance MaybeNF Bool where
  maybeDeepSeq = deepseq

instance MaybeNF Int where
  maybeDeepSeq = deepseq

instance MaybeNF Word where
  maybeDeepSeq = deepseq

instance MaybeNF Int64 where
  maybeDeepSeq = deepseq

instance MaybeNF Word64 where
  maybeDeepSeq = deepseq

instance MaybeNF Float where
  maybeDeepSeq = deepseq

instance MaybeNF Double where
  maybeDeepSeq = deepseq

instance MaybeNF () where
  maybeDeepSeq = deepseq

instance (MaybeNF a, MaybeNF b) => MaybeNF (a, b) where
  maybeDeepSeq (a,b) x = a `maybeDeepSeq` b `maybeDeepSeq` x

instance (MaybeNF a, MaybeNF b, MaybeNF c) => MaybeNF (a, b, c) where
  maybeDeepSeq (a,b,c) x = a `maybeDeepSeq` b `maybeDeepSeq` c `maybeDeepSeq` x


while cond step init = loop init
  where loop s | cond s = loop (step s)
               | True   = s
{-# INLINE [0] while #-}

whileM :: Monad m => (a -> Bool) -> (a -> a) -> (a -> m ()) ->  a -> m ()
whileM cond step action init
  = let loop !s = if cond s 
                 then action s >> loop (step s)
                 else P.return ()
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

