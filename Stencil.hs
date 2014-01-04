{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
module Stencil where

import qualified Prelude as P
import Prelude ((.),($),Num(..),Maybe(..),otherwise,undefined,Int,Bool(..),const)

import Frontend as F
import Core
import HOAS as H hiding (Z)

infixl 7 *>
infixl 6 +^
infixl 6 -^

(*>) :: Shape sh -> Expr Int -> Shape sh
sh *> i = mapShape (*i) sh

(-^) :: Shape sh -> Shape sh -> Shape sh
sh1 -^ sh2 = zipShape (-) sh1 sh2

(+^) :: Shape sh -> Shape sh -> Shape sh
sh1 +^ sh2 = zipShape (+) sh1 sh2

maxShape :: Shape sh -> Shape sh -> Shape sh
maxShape sh1 sh2 = zipShape max sh1 sh2

minShape :: Shape sh -> Shape sh -> Shape sh
minShape sh1 sh2 = zipShape min sh1 sh2

clampShape :: Shape sh -> Shape sh -> Shape sh
clampShape bounds sh = zipShape (\b i -> min (b-1) (max 0 i)) bounds sh

data Boundary a = BoundConst a
                | BoundClamp

data Stencil sh a b = forall s. Computable s => Stencil
  { stencilSize :: Shape sh
  , sizeF :: Shape sh -> Shape sh
  , init :: (Shape sh -> a) -> s
  , step :: (Shape sh -> a) -> s -> s
  , write :: s -> Shape sh -> (Shape sh -> b -> M ()) -> M ()
  }


runStencil :: Computable a => Boundary a -> Stencil (sh :. Expr Int) a b -> Pull (sh :. Expr Int) a -> Push (sh :. Expr Int) b
runStencil boundary (Stencil stSize sizeF init step write) (Pull ixf sh) = Push f (sizeF sh)
  where c = runStencilRegion init step write ixfC (centralRegion sh borderSize)
        borderSize = mapShape (`quot` 2) stSize
        ixfC shBase ix = ixf (offset shBase ix)
        ixfB shBase ix = 
          let ix' = offset shBase ix 
          in  case boundary of
            BoundConst z ->
              if_ (boundsCheck sh ix')
                (ixf ix')
                z
            BoundClamp ->
                ixf (clampShape sh ix')
        b k r = runStencilRegion init step write ixfB r k
        f k =
          do c k
             P.mapM_ (b k) (borderRegions sh borderSize)

runStencilRegion :: Computable s
                 => ((Shape sh -> a) -> s) -- Init
                 -> ((Shape sh -> a) -> s -> s) -- Step
                 -> (s -> Shape sh -> (Shape sh -> b -> M ()) -> M ()) -- Write
                 -> (Shape sh -> (Shape sh -> a))
                 -> (Shape sh, Shape sh) -- Region
                 -> (Shape sh -> b -> M ())
                 -> M ()
runStencilRegion init step write ixf ((sh1 :. l1), (sh2 :. l2)) k =
  forRegion sh1 sh2 (\ish ->
    if_ (l1 < l2)
      (rec (\f (i,s) ->
        write s (ish :. i) k P.>>
        if_ (i+1 < l2)
          (f (i+1, step (ixf (ish :. (i+1))) s))
          (P.return ()))
        (l1, init $ ixf (ish :. l1)))
      (P.return ()))
    --let step' i s = if_ (i < l2) 
    --                    (step (ixf (ish :. i)) s)
    --                    s
    --in 
    --whileE (\(i,s) -> i < l2)
    --  (\(i,s) -> (i+1, step' (i+1) s)) --) --(i+1, init (ixf (ish :. i)))
    --  (\(i,s) -> write s (ish :. i) k)
    --  (l1, init $ ixf (ish :. l1)))

boundsCheck :: Shape sh -> Shape sh -> Expr Bool
boundsCheck Z         Z          = true
boundsCheck (sh :. b) (ish :. i) = i >= 0 && i < b && boundsCheck sh ish

centralRegion :: Shape sh -> Shape sh -> (Shape sh, Shape sh)
centralRegion sh borderSize = (borderSize, (sh -^ borderSize))

borderRegions :: Shape sh               -- Whole shape
              -> Shape sh               -- Border size
              -> [(Shape sh, Shape sh)] -- List of border regions
borderRegions Z          Z          = []
borderRegions (shL :. l) (shB :. b) = r1 : r2 : rs
  where sh0 = mapShape (const 0) shL
        r1 = (sh0 :. 0      , shL :. b)
        r2 = (sh0 :. (l - b), shL :. l)
        rs = P.map f (borderRegions shL shB)
        f (sh1,sh2) = (sh1 :. b, sh2 :. (l - b))


forRegion :: Shape sh -> Shape sh -> (Shape sh -> M ()) -> M ()
forRegion sh1 sh2 k = 
  forShape
    sh
    (k . (sh1 +^) . (fromIndex sh))
  where sh = sh2 -^ sh1

iterateM :: Expr Int -> (Expr Int -> M ()) -> M ()
iterateM n action = whileE (\i -> i > n) (+1) action 0



class Tup t => UTup t a | t -> a where
  tupMap2 :: (m a -> n a) -> t m -> t n 
  tupZip :: (m1 a -> m2 a -> m3 a) -> t m1 -> t m2 -> t m3
  tupMap3 :: (m a -> n a) -> t m -> [n a]

instance UTup (Ein a) a where
  tupMap2 f (Ein a) = Ein (f a)
  tupZip f (Ein a) (Ein b) = Ein (a `f` b)
  tupMap3 f (Ein a) = [f a]

instance UTup as a => UTup (Cons a as) a where
  tupMap2 f (a ::. as) = f a ::. tupMap2 f as
  tupZip f (a ::. as) (b ::. bs) = a `f` b ::. tupZip f as bs
  tupMap3 f (a ::. as) = f a : tupMap3 f as

data Thing a = Thing (Int,Int) (Expr a)

newtype GetFun t a = GetFun { unGetFun :: Expr (t Id) -> Expr a }

data GetThing t a = GetThing (Int,Int) (Expr (t Id) -> Expr a)

makeStencil2 :: (Num a, Storable a, UTup t a, TupTypeable t) => Int -> Int -> t Thing -> t (GetFun t) -> Stencil DIM2 (Expr a) (Expr a)
makeStencil2 sizeX sizeY t gt =
  Stencil 
    { stencilSize = F.Z :. numLit sizeY :. numLit sizeX
    , sizeF = P.id
    , init = initF t
    , step = stepF t gt (1,0)
    , write = writeF t gt
    }

numLit :: (P.Integral a, Storable a) => a -> Expr a
numLit = fromInteger . P.toInteger

toShapeDim2 :: (Int,Int) -> Shape DIM2
toShapeDim2 (x,y) = F.Z :. numLit y :. numLit x

initF :: (UTup t a, Storable a, Num a) => t Thing -> (Shape DIM2 -> Expr a) -> Expr (t Id)
initF t f = TupN (tupMap2 g t)
  where g (Thing p a) = f (toShapeDim2 p)

stepF :: (UTup t a, Storable a, Num a) => t Thing -> t (GetFun t) -> (Int,Int) -> (Shape DIM2 -> Expr a) -> Expr (t Id) -> Expr (t Id)
stepF t gt (sx,sy) f s = TupN $ tupMap2 chooseExpr t
  where shifted = tupMap3 P.id $ tupZip (\(Thing (x,y) e) (GetFun f) -> GetThing (x - sx,y - sy) f) t gt
        lookup p [] = Nothing
        lookup p (GetThing p' g : ts) | p P.== p' = Just g
                                      | otherwise = lookup p ts
        chooseExpr (Thing p a) =
          case lookup p shifted of
            Just get -> get s
            Nothing  -> f (toShapeDim2 p)

writeF :: (UTup t a, Storable a, Num a) => t Thing -> t (GetFun t) -> Expr (t Id) -> Shape DIM2 -> (Shape DIM2 -> (Expr a) -> M ()) -> M ()
writeF t gt s sh w = w sh (P.foldl1 (+) exprs)
  where exprs = tupMap3 P.id x
        x = tupZip (\(Thing p a) (GetFun get) -> get s * a) t gt

data ThingE t a = ThingE (Int,Int) (t Expr -> Expr a)

makeStencil2E :: (Num a, Storable a, UTup t a, TupTypeable t) => Int -> Int -> Int -> Int -> t (ThingE t) -> t (GetFun t) -> Stencil DIM2 (Expr a) (Expr a)
makeStencil2E inSizeX inSizeY outSizeX outSizeY t gt =
  Stencil
    { stencilSize = F.Z :. numLit inSizeY :. numLit inSizeX
    , sizeF = undefined
    , init = \ixf -> ixf (Z :. 0 :. 0)
    , step = undefined
    , write = undefined
    }
