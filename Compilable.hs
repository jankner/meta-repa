{-# LANGUAGE GADTs, TypeFamilies, TypeOperators, FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell #-}
module Compilable where

import HOAS hiding (Z)
import Frontend
import qualified Data.Array.Repa as R
import TestRepr

import Data.Vector.Unboxed

import Prelude as P

import Language.Haskell.TH hiding (Type)
import Language.Haskell.TH.Syntax hiding (Type)


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
      ,Shapely sh
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


class R.Shape (RecSh sht) => RShTup sht where
  type RecSh sht
  reconstructShape :: sht -> RecSh sht

instance RShTup () where
  type RecSh () = R.Z
  reconstructShape () = R.Z

instance RShTup sht => RShTup (Int, sht) where
  type RecSh (Int, sht) = (RecSh sht) R.:. Int
  reconstructShape (i, sht) = reconstructShape sht R.:. i


class (Computable (AsTup sh)
      ,Shapely sh
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
  
proxyFromShape :: Shape sh -> ShProxy sh
proxyFromShape Z = PZ
proxyFromShape (sh :. _) = PSnoc (proxyFromShape sh)

type family Meta a
type instance Meta ()       = ()
type instance Meta (Expr a) = a
type instance Meta (a, b)   = (Meta a, Meta b)
type instance Meta (M a)    = IO (Meta a)
type instance Meta (a -> b) = Meta a -> Meta b

type family ToRepaSh a
type instance ToRepaSh Z         = R.Z
type instance ToRepaSh (sh :. Expr Length) = ToRepaSh sh R.:. Int


instance Lift (Proxy a) where
  lift (PExpr a)             = conE 'PExpr `appE` lift a
  lift (PExprArg a p)        = conE 'PExprArg `appE` lift a `appE` lift p
  lift (PManifest sh a)      = conE 'PManifest `appE` lift sh `appE` lift a
  lift (PManifestArg sh a p) = conE 'PManifestArg `appE` lift sh `appE` lift a `appE` lift p

instance Lift (ShProxy sh) where 
  lift PZ = conE 'PZ
  lift (PSnoc p) = conE 'PSnoc `appE` lift p

data Proxy a where
  PExpr :: Type a -> Proxy (Expr a)
  PExprArg :: Type a -> Proxy f -> Proxy (Expr a -> f)
  PManifest :: ShProxy sh -> CProxy a -> Proxy (MManifest sh a)
  PManifestArg :: ShProxy sh -> CProxy a -> Proxy f -> Proxy (MManifest sh a -> f)

data ShProxy sh where
  PZ :: ShProxy Z
  PSnoc :: ShProxy sh -> ShProxy (sh :. Expr Int)


class Computable (GenTy f) => Compilable f where
  type GenTy f
  type External f
  compile :: f -> GenTy f
  reconstruct :: Proxy f -> (Meta (GenTy f)) -> External f
  proxyOf :: f -> Proxy f

instance Typeable a => Compilable (Expr a) where 
  type GenTy (Expr a) = Expr a
  type External (Expr a) = a
  compile e = e
  reconstruct (PExpr t) a = a
  proxyOf e = PExpr typeOf0

instance (Typeable a, Compilable f) => Compilable (Expr a -> f) where
  type GenTy (Expr a -> f) = Expr a -> GenTy f
  type External (Expr a -> f) = a -> External f
  compile f = \a -> compile (f a)
  reconstruct (PExprArg _ p) f = \a -> reconstruct p (f a)
  proxyOf f = PExprArg typeOf0 (proxyOf undefined)

--instance (Computable a, Storable (Internal a), ShTup sh) => Compilable (Pull sh a) where
--  type GenTy (Pull sh a) = (Expr (IArray (Internal a)), AsTup sh)
--  type External (Pull sh a) = Manifest (ToRepaSh sh) (Internal a)
--  compile arr@(Pull ixf sh) = (runMutableArray (storePull arr), compileShape sh)
--  reconstruct _ (arr, sht) = Manifest arr (reconstructShape sht)
--
--instance (Computable a, Storable (Internal a), ShTup sh) => Compilable (Push sh a) where
--  type GenTy (Push sh a) = (Expr (IArray (Internal a)), AsTup sh)
--  type External (Push sh a) = Manifest (ToRepaSh sh) (Internal a)
--  compile arr@(Push ixf sh) = (runMutableArray (storePush arr), compileShape sh)
--  reconstruct _ (arr, sht) = Manifest arr (reconstructShape sht)

instance (Computable a, Storable (Internal a), ShTup sh) => Compilable (MManifest sh a) where
  type GenTy (MManifest sh a) = (Expr (IArray (Internal a)), AsTup sh)
  type External (MManifest sh a) = R.Array R.U (ToRepaSh sh) (Internal a)
  compile (MManifest arr sh) = (arr, compileShape sh)
  reconstruct (PManifest _ _) (arr, sht) = R.fromUnboxed (reconstructShape sht) arr
  proxyOf m = PManifest (proxyFromShape (fakeShape "")) cProxy

instance (Computable a, Storable (Internal a), ShFun sh (GenTy f), Compilable f) 
         => Compilable (MManifest sh a -> f) where
  type GenTy (MManifest sh a -> f) = Expr (IArray (Internal a)) -> Fun sh  (GenTy f)
  type External (MManifest sh a -> f) = R.Array R.U (ToRepaSh sh) (Internal a) -> (External f)
  compile f = \arr -> shFun ((\sh -> compile $ f (mmanifestFromArr sh arr)) :: Shape sh -> GenTy f)
  reconstruct (PManifestArg _ _ p) f = \uarr -> 
    let arr = R.toUnboxed uarr
        sh  = R.extent uarr
    in reconstruct p (rshFun (f arr) sh)
  proxyOf f = PManifestArg (proxyFromShape (fakeShape "")) cProxy (proxyOf undefined)

--instance (Computable a, Storable (Internal a), ShTup sh) => Compilable (MManifest sh a) where
--  type GenTy (MManifest sh a) = (Expr (IArray (Internal a)), AsTup sh)
--  type External (MManifest sh a) = Manifest (ToRepaSh sh) (Internal a)
--  compile (MManifest arr sh) = (arr, compileShape sh)
--  reconstruct (PManifest _ _) (arr, sht) = Manifest arr (reconstructShape sht)
--  proxyOf m = PManifest (proxyFromShape (fakeShape "")) cProxy
--
--instance (Computable a, Storable (Internal a), ShFun sh (GenTy f), Compilable f) 
--         => Compilable (MManifest sh a -> f) where
--  type GenTy (MManifest sh a -> f) = Expr (IArray (Internal a)) -> Fun sh  (GenTy f)
--  type External (MManifest sh a -> f) = Manifest (ToRepaSh sh) (Internal a) -> (External f)
--  compile f = \arr -> shFun ((\sh -> compile $ f (mmanifestFromArr sh arr)) :: Shape sh -> GenTy f)
--  reconstruct (PManifestArg _ _ p) f = \(Manifest arr sh) -> reconstruct p (rshFun (f arr) sh)
--  proxyOf f = PManifestArg (proxyFromShape (fakeShape "")) cProxy (proxyOf undefined)

--instance (Storable a, ShFun sh (GenTy f), Compilable f) 
--         => Compilable (Pull sh (Expr a) -> f) where
--  type GenTy (Pull sh (Expr a) -> f)    = Expr (IArray a) -> Fun sh  (GenTy f)
--  type External (Pull sh (Expr a) -> f) = Manifest (ToRepaSh sh) a -> (External f)
--  compile f = \arr -> shFun ((\sh -> compile $ f (pullFromArr sh arr)) :: Shape sh -> GenTy f)
--  reconstruct _ f = \(Manifest arr sh) -> reconstruct (undefined :: f) $ rshFun (f arr) sh

mmanifestFromArr :: (Computable a, Storable (Internal a)) => Shape sh -> Expr (IArray (Internal a)) -> MManifest sh a
mmanifestFromArr sh arr = MManifest arr sh

pullFromArr :: Storable a => Shape sh -> Expr (IArray a) -> Pull sh (Expr a)
pullFromArr sh arr = Pull (\ix -> readIArray arr (toIndex sh ix)) sh

