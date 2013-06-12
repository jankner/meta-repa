{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Compilable where

import HOAS hiding (Z)
import Frontend
import qualified Data.Array.Repa as R
import TestRepr

import Data.Vector.Unboxed

import Prelude as P


class R.Shape sh => RShFun sh a where
  type RFun sh a
  rshFun :: RFun sh a -> (sh -> a)

instance RShFun R.Z a where
  type RFun R.Z a = a
  rshFun a = P.const a

instance RShFun sh a => RShFun (sh R.:. Int) a where
  type RFun (sh R.:. Int) a = Int -> RFun sh a
  rshFun f = \(sh R.:. i) -> rshFun (f i) sh


class (Computable (Fun sh a)
      ,RShFun (ToRepaSh sh) (Meta a)
      ,RFun (ToRepaSh sh) (Meta a) ~ Meta (Fun sh a))
      => ShFun sh a where
  type Fun sh a
  shFun :: (Shape sh -> a) -> Fun sh a

instance Computable a => ShFun Z a where
  type Fun Z a = a
  shFun f = f Z

instance ShFun sh a => ShFun (sh :. Expr Length) a where
  type Fun (sh :. Expr Length) a = Expr Length -> Fun sh a
  shFun f = \i -> shFun (\sh -> f (sh :. i))


class RShTup sht where
  type RecSh sht
  reconstructShape :: sht -> RecSh sht

instance RShTup () where
  type RecSh () = R.Z
  reconstructShape () = R.Z

instance RShTup sht => RShTup (i, sht) where
  type RecSh (i, sht) = (RecSh sht) R.:. i
  reconstructShape (i, sht) = reconstructShape sht R.:. i


class (Computable (AsTup sh)
      ,RShTup (Meta (AsTup sh))
      ,ToRepaSh sh ~ RecSh (Meta (AsTup sh)))
      => ShTup sh where
  type AsTup sh
  compileShape :: Shape sh -> AsTup sh

instance ShTup Z where
  type AsTup Z = ()
  compileShape Z = ()

instance ShTup sh => ShTup (sh :. Expr Length) where
  type AsTup (sh :. Expr Length) = (Expr Length, AsTup sh)
  compileShape (sh :. i) = (i, compileShape sh)
  

type family Meta a
type instance Meta ()       = ()
type instance Meta (Expr a) = a
type instance Meta (a, b)   = (Meta a, Meta b)
type instance Meta (M a)    = IO (Meta a)
type instance Meta (a -> b) = Meta a -> Meta b

type family ToRepaSh a
type instance ToRepaSh Z         = R.Z
type instance ToRepaSh (sh :. Expr Length) = ToRepaSh sh R.:. Int


class Computable (GenTy f) => Compilable f where
  type GenTy f
  type External f
  compile :: f -> GenTy f
  reconstruct :: f -> (Meta (GenTy f)) -> External f

instance Typeable a => Compilable (Expr a) where 
  type GenTy (Expr a) = Expr a
  type External (Expr a) = a
  compile e = e
  reconstruct _ a = a

instance (Typeable a, Compilable f) => Compilable (Expr a -> f) where
  type GenTy (Expr a -> f) = Expr a -> GenTy f
  type External (Expr a -> f) = a -> External f
  compile f = \a -> compile (f a)
  reconstruct _ f = \a -> reconstruct (undefined :: f) (f a)

instance (Computable a, Storable (Internal a), ShTup sh) => Compilable (Pull sh a) where
  type GenTy (Pull sh a) = (Expr (IArray (Internal a)), AsTup sh)
  type External (Pull sh a) = Manifest (ToRepaSh sh) (Internal a)
  compile arr@(Pull ixf sh) = (runMutableArray (storePull arr), compileShape sh)
  reconstruct _ (arr, sht) = Manifest arr (reconstructShape sht)

instance (Computable a, Storable (Internal a), ShTup sh) => Compilable (Push sh a) where
  type GenTy (Push sh a) = (Expr (IArray (Internal a)), AsTup sh)
  type External (Push sh a) = Manifest (ToRepaSh sh) (Internal a)
  compile arr@(Push ixf sh) = (runMutableArray (storePush arr), compileShape sh)
  reconstruct _ (arr, sht) = Manifest arr (reconstructShape sht)

instance (Storable a, ShFun sh (GenTy f), Compilable f) 
         => Compilable (Pull sh (Expr a) -> f) where
  type GenTy (Pull sh (Expr a) -> f)    = Expr (IArray a) -> Fun sh  (GenTy f)
  type External (Pull sh (Expr a) -> f) = Manifest (ToRepaSh sh) a -> (External f)
  compile f = \arr -> shFun ((\sh -> compile $ f (pullFromArr sh arr)) :: Shape sh -> GenTy f)
  reconstruct _ f = \(Manifest arr sh) -> reconstruct (undefined :: f) $ rshFun (f arr) sh

pullFromArr :: Storable a => Shape sh -> Expr (IArray a) -> Pull sh (Expr a)
pullFromArr sh arr = Pull (\ix -> readIArray arr (toIndex sh ix)) sh

