module MaybeNF where

infixr 0 `maybeDeepSeq`

class MaybeNF a where
  maybeDeepSeq :: a -> b -> b
