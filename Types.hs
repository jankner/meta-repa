{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types where

import Data.IORef
import qualified Data.Map as M
import qualified Data.Set as S


data Class = CEq | COrd | CNum | CIntegral | CShow
  deriving (Eq,Ord,Show)

type TRef = IORef (Maybe Type)

data Type = TVar TypeVar
          | TConst TypeConst
          | TTup2 Type Type
          | TMArr Type
          | TIArr Type
          | TFun Type Type
          | TIO Type
  deriving (Eq,Ord)

instance Show Type where
  showsPrec d (TVar v) = shows v
  showsPrec d (TConst t) = shows t
  showsPrec d (TTup2 t1 t2) = showString "(" . showsPrec 1 t1 . showString "," . showsPrec 1 t2 . showString ")"
  showsPrec d (TMArr t) = showString "{" . showsPrec 1 t . showString "}"
  showsPrec d (TIArr t) = showString "[" . showsPrec 1 t . showString "]"
  showsPrec d (TFun t1 t2) = showParen (d > 9) $ showsPrec 10 t1 . showString " -> " . showsPrec 10 t2
  showsPrec d (TIO t) = showParen (d > 10) $ showString "IO " . showsPrec 11 t

data TypeVar = TypeVar Int TRef
  deriving Eq

instance Ord TypeVar where
  compare (TypeVar v1 _) (TypeVar v2 _) = compare v1 v2

type Uniq = Int

uniq :: TypeVar -> Uniq
uniq (TypeVar v _) = v

tRef :: TypeVar -> TRef
tRef (TypeVar _ ref) = ref

instance Show TypeVar where
  show (TypeVar v _) = "a" ++ (show v)

data TypeConst = TBool | TInt | TUnit
  deriving (Eq,Ord)

instance Show TypeConst where
  show TInt  = "Int"
  show TBool = "Bool"
  show TUnit = "()"

tInt  = TConst TInt
tBool = TConst TBool
tUnit = TConst TUnit

infixr 9 -->
(-->) :: Type -> Type -> Type
(-->) = TFun

type Env = [(Int,Type)]

type Subst = M.Map TypeVar Type

applySubst :: Subst -> Type -> Type
applySubst subst (TVar v) = M.findWithDefault (TVar v) v subst
applySubst subst (TTup2 s1 s2) = TTup2 (applySubst subst s1) (applySubst subst s2)
applySubst subst (TFun  s1 s2) = TFun  (applySubst subst s1) (applySubst subst s2)
applySubst subst (TMArr s) = TMArr (applySubst subst s)
applySubst subst (TIArr s) = TIArr (applySubst subst s)
applySubst subst (TIO   s) = TIO   (applySubst subst s)
applySubst subst s = s

infixr 9 |.|
(|.|) :: Subst -> Subst -> Subst
s1 |.| s2 = M.unionWith f s1 s2
  where f t1 t2 = applySubst s1 t2

type SortContext = M.Map Uniq (S.Set Class)

