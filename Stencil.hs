{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Stencil where

import qualified Prelude as P
import Prelude ((.),($),Num(..),Int,Bool,const,map,)

import Frontend
import Core
import HOAS

infixl 7 *>
infixl 6 +^
infixl 6 -^

(*>) :: Shape sh -> Expr Int -> Shape sh
sh *> i = mapShape (*i) sh

(-^) :: Shape sh -> Shape sh -> Shape sh
sh1 -^ sh2 = zipShape (-) sh1 sh2

(+^) :: Shape sh -> Shape sh -> Shape sh
sh1 +^ sh2 = zipShape (+) sh1 sh2


data Stencil sh a b = forall s. Computable s => Stencil
  { defaultValue :: a
  , stencilSize :: Shape sh
  , sizeF :: Shape sh -> Shape sh
  , init :: Pull sh a -> s
  , step :: Pull sh a -> s -> s
  , write :: s -> Shape sh -> (Shape sh -> b -> M ()) -> M ()
  }


runStencil :: Computable a => Stencil (sh :. Expr Int) a b -> Pull (sh :. Expr Int) a -> Push (sh :. Expr Int) b
runStencil (Stencil z stSize@(stSh :. stL) sizeF init step write) (Pull ixf sh@(sh1 :. l1)) = Push f (sizeF sh)
  where c = runStencilRegion init step write pullC (centralRegion sh borderSize)
        borderSize = mapShape (`quot` 2) stSize
        pullC shBase = Pull (\ix -> ixf (offset shBase ix)) stSize
        pullB shBase = Pull (\ix -> let ix' = offset shBase ix 
                                    in if_ (boundsCheck sh ix')
                                          (ixf ix')
                                          z)
                            stSize
        b k r = runStencilRegion init step write pullB r k
        f k =
          do c k
             P.mapM_ (b k) (borderRegions sh stSize)

runStencilRegion :: Computable s
                 => (Pull sh a -> s) -- Init
                 -> (Pull sh a -> s -> s) -- Step
                 -> (s -> Shape sh -> (Shape sh -> b -> M ()) -> M ()) -- Write
                 -> (Shape sh -> Pull sh a)
                 -> (Shape sh, Shape sh) -- Region
                 -> (Shape sh -> b -> M ())
                 -> M ()
runStencilRegion init step write pull ((sh1 :. l1), (sh2 :. l2)) k =
  forRegion sh1 sh2 (\ish ->
    whileE (\(i,s) -> i < l2)
      (\(i,s) -> (i+1, step (pull (ish :. i)) s))
      (\(i,s) -> write s (ish :. i) k)
      (l1, init $ pull (ish :. l1)))

boundsCheck :: Shape sh -> Shape sh -> Expr Bool
boundsCheck (sh :. b) (ish :. i) = i >= 0 && i < b && boundsCheck sh ish

centralRegion :: Shape sh -> Shape sh -> (Shape sh, Shape sh)
centralRegion sh borderSize = (borderSize, (sh -^ borderSize))

borderRegions :: Shape sh               -- Whole shape
              -> Shape sh               -- Border size
              -> [(Shape sh, Shape sh)] -- List of border regions
borderRegions (shL :. l) (shB :. b) = r1 : r2 : rs
  where sh0 = mapShape (const 0) shL
        r1 = (sh0 :. 0      , shL :. b)
        r2 = (sh0 :. (l - b), shL :. l)
        rs = map f (borderRegions shL shB)
        f (sh1,sh2) = (sh1 :. b, sh2 :. (l - b))


forRegion :: Shape sh -> Shape sh -> (Shape sh -> M ()) -> M ()
forRegion sh1 sh2 k = 
  forShape
    sh
    (k . (sh1 +^) . (fromIndex sh))
  where sh = sh2 -^ sh1

iterateM :: Expr Int -> (Expr Int -> M ()) -> M ()
iterateM n action = whileE (\i -> i > n) (+1) action 0

