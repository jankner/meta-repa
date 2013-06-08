{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Types
  ( Class(..)
  , Type(..)
  , TypeConst(..)
  , tInt
  , tInt64
  , tWord
  , tWord64
  , tFloat
  , tDouble
  , tBool
  , tUnit
  , (-->)
  , Env
  ) where


data Class = CEq 
           | COrd
           | CNum
           | CIntegral
           | CBits
           | CFloating
           | CFractional
           | CShow
  deriving (Eq,Ord,Show)

data Type = TConst TypeConst
          | TTup2 Type Type
          | TTupN [Type]
          | TMArr Type
          | TIArr Type
          | TFun Type Type
          | TIO Type
  deriving (Eq,Ord)

instance Show Type where
  showsPrec d (TConst t) = shows t
  showsPrec d (TTup2 t1 t2) = showString "(" . showsPrec 1 t1 . showString "," . showsPrec 1 t2 . showString ")"
  showsPrec d (TTupN ts) = showString "(" . showsTup ts
  showsPrec d (TMArr t) = showString "{" . showsPrec 1 t . showString "}"
  showsPrec d (TIArr t) = showString "[" . showsPrec 1 t . showString "]"
  showsPrec d (TFun t1 t2) = showParen (d > 9) $ showsPrec 10 t1 . showString " -> " . showsPrec 10 t2
  showsPrec d (TIO t) = showParen (d > 10) $ showString "IO " . showsPrec 11 t

showsTup (a:[]) = showsPrec 0 a . showString ")"
showsTup (a:as) = showsPrec 0 a . showString "," . showsTup as

data TypeConst = TInt
               | TInt64
               | TWord
               | TWord64
               | TFloat
               | TDouble
               | TBool
               | TUnit
  deriving (Eq,Ord)

instance Show TypeConst where
  show TInt = "Int"
  show TInt64 = "Int64"
  show TWord = "Word"
  show TWord64 = "Word64"
  show TFloat = "Float"
  show TDouble = "Double"
  show TBool = "Bool"
  show TUnit = "()"

tInt = TConst TInt
tInt64 = TConst TInt64
tWord = TConst TWord
tWord64 = TConst TWord64
tFloat = TConst TFloat
tDouble = TConst TDouble
tBool = TConst TBool
tUnit = TConst TUnit

infixr 9 -->
(-->) :: Type -> Type -> Type
(-->) = TFun

type Env = [(Int,Type)]

