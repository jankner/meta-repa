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
  rshFun :: RFun sh a -> sh -> a
  rshFunF :: (sh -> a) -> RFun sh a

instance RShFun R.Z a where
  type RFun R.Z a = a
  rshFun a = P.const a
  rshFunF f = f R.Z

instance RShFun sh a => RShFun (sh R.:. Int) a where
  type RFun (sh R.:. Int) a = Int -> RFun sh a
  rshFun f = \(sh R.:. i) -> rshFun (f i) sh
  rshFunF f = \i -> rshFunF (\sh -> f (sh R.:. i))


class (Computable a
      ,Computable (Fun sh a)
      ,Shapely sh
      ,RShFun (ToRepaSh sh) (Internal a)
      ,RFun (ToRepaSh sh) (Internal a) ~ Internal (Fun sh a))
      => ShFun sh a where
  type Fun sh a
  shFun :: (Shape sh -> a) -> Fun sh a
  shFunR :: Fun sh a -> Shape sh -> a

instance Computable a => ShFun Z a where
  type Fun Z a = a
  shFun f = f Z
  shFunR a = P.const a

instance ShFun sh a => ShFun (sh :. Expr Length) a where
  type Fun (sh :. Expr Length) a = Expr Length -> Fun sh a
  shFun f = \i -> shFun (\sh -> f (sh :. i))
  shFunR f = \(sh :. i) -> shFunR (f i) sh


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
      ,RShTup (Internal (AsTup sh))
      ,ToRepaSh sh ~ RecSh (Internal (AsTup sh)))
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

type family ToRepaSh a
type instance ToRepaSh Z         = R.Z
type instance ToRepaSh (sh :. Expr Length) = ToRepaSh sh R.:. Int


instance Lift (Proxy a) where
  lift (PExpr a)             = conE 'PExpr `appE` lift a
  lift (PExprArg a p)        = conE 'PExprArg `appE` lift a `appE` lift p
  lift (PManifest sh a)      = conE 'PManifest `appE` lift sh `appE` lift a
  lift (PManifestArg sh a p) = conE 'PManifestArg `appE` lift sh `appE` lift a `appE` lift p
  lift (PPull sh a)          = conE 'PPull `appE` lift sh `appE` lift a
  lift (PPullArg sh a p)     = conE 'PPullArg `appE` lift sh `appE` lift a `appE` lift p

instance Lift (ShProxy sh) where 
  lift PZ = conE 'PZ
  lift (PSnoc p) = conE 'PSnoc `appE` lift p

data Proxy a where
  PExpr :: Type a -> Proxy (Expr a)
  PExprArg :: Type a -> Proxy f -> Proxy (Expr a -> f)
  PManifest :: ShProxy sh -> CProxy a -> Proxy (MManifest sh a)
  PManifestArg :: ShProxy sh -> CProxy a -> Proxy f -> Proxy (MManifest sh a -> f)
  PPull :: ShProxy sh -> CProxy a -> Proxy (Pull sh a)
  PPullArg :: ShProxy sh -> CProxy a -> Proxy f -> Proxy (Pull sh a -> f)

data ShProxy sh where
  PZ :: ShProxy Z
  PSnoc :: ShProxy sh -> ShProxy (sh :. Expr Int)


class Computable (GenTy f) => Compilable f where
  type GenTy f
  type External f
  compile :: f -> GenTy f
  reconstruct :: Proxy f -> (Internal (GenTy f)) -> External f
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

instance (Computable a, ShTup sh, ShFun sh a)
         => Compilable (Pull sh a) where
  type GenTy (Pull sh a) = (Fun sh a, AsTup sh)
  type External (Pull sh a) = R.Array R.D (ToRepaSh sh) (Internal a)
  compile arr@(Pull ixf sh) = (shFun ixf, compileShape sh)
  reconstruct _ (ixf, sht) = R.fromFunction (reconstructShape sht) (rshFun ixf)
  proxyOf f = PPull (proxyFromShape (fakeShape "")) cProxy

instance (Computable a, ShFun sh a, ShFun sh (GenTy f), Compilable f) 
         => Compilable (Pull sh a -> f) where
  type GenTy (Pull sh a -> f) = Fun sh a -> Fun sh (GenTy f)
  type External (Pull sh a -> f) = R.Array R.D (ToRepaSh sh) (Internal a) -> (External f)
  compile f = \ixf -> shFun ((\sh -> compile $ f (fromFunction (shFunR ixf) sh)) :: Shape sh -> GenTy f)
  reconstruct (PPullArg _ _ p) f = \arr ->
    let (sh, ixf) = R.toFunction arr
    in  reconstruct p (rshFun (f (rshFunF ixf)) sh)
  proxyOf f = PPullArg (proxyFromShape (fakeShape "")) cProxy (proxyOf undefined)

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

mmanifestFromArr :: (Computable a, Storable (Internal a)) => Shape sh -> Expr (IArray (Internal a)) -> MManifest sh a
mmanifestFromArr sh arr = MManifest arr sh

pullFromArr :: Storable a => Shape sh -> Expr (IArray a) -> Pull sh (Expr a)
pullFromArr sh arr = Pull (\ix -> readIArray arr (toIndex sh ix)) sh

