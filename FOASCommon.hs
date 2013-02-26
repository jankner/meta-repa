module FOASCommon where


data BinOp = Plus  -- Num a => P a
           | Minus -- Num a => P a
           | Mult  -- Num a => P a
           | Quot -- Integral a => P a
           | Rem  -- Integral a => P a
           | Min -- Ord a => P a
           | Max -- Ord a => P a
           | And -- P Bool
           | Or  -- P Bool
  deriving (Show, Eq, Ord)

data CompOp = EQU  -- Eq a => CompOp a
            | NEQ -- Eq a => CompOp a
            | GTH -- Ord a => CompOp a
            | LTH -- Ord a => CompOp a
            | GEQ -- Ord a => CompOp a
            | LEQ -- Ord a => CompOp a
  deriving (Show, Eq, Ord)

