module FOASCommon where


data BinOp = Plus  -- Num a => P a
           | Minus -- Num a => P a
           | Mult  -- Num a => P a
           | Quot -- Integral a => P a
           | Rem  -- Integral a => P a
           | Div  -- Integral a => P a
           | Mod  -- Integral a => P a
           | FDiv -- Fractional a => P a
           | Min -- Ord a => P a
           | Max -- Ord a => P a
           | And -- P Bool
           | Or  -- P Bool
           | Xor -- Bits a => P a
           | BAnd -- Bits a => P a
           | BOr -- Bits a => P a
           | Pow -- Floating a
  deriving (Show, Eq, Ord)

data UnOp = Abs    -- Num a
          | Signum -- Num a
          | Recip  -- Fractional a
          | Complement -- Bits a
          | Exp  -- Floating a
          | Sqrt -- Floating a
          | Log  -- Floating a
          | Sin  -- Floating a
          | Tan  -- Floating a
          | Cos  -- Floating a
          | ASin -- Floating a
          | ATan -- Floating a
          | ACos -- Floating a
  deriving (Show, Eq, Ord)

data CompOp = EQU  -- Eq a => CompOp a
            | NEQ -- Eq a => CompOp a
            | GTH -- Ord a => CompOp a
            | LTH -- Ord a => CompOp a
            | GEQ -- Ord a => CompOp a
            | LEQ -- Ord a => CompOp a
  deriving (Show, Eq, Ord)


showBinOp :: Show a => Int -> BinOp -> a -> a -> ShowS
showBinOp d Minus a b = showParen (d > 6) $ showsPrec 6 a . showString " - " . showsPrec 7 b
showBinOp d Plus  a b = showParen (d > 6) $ showsPrec 6 a . showString " + " . showsPrec 7 b
showBinOp d Mult  a b = showParen (d > 7) $ showsPrec 7 a . showString " * " . showsPrec 8 b
showBinOp d Quot  a b = showParen (d > 7) $ showsPrec 7 a . showString " `quot` " . showsPrec 8 b
showBinOp d Rem   a b = showParen (d > 7) $ showsPrec 7 a . showString " `rem` " . showsPrec 8 b
showBinOp d Div   a b = showParen (d > 7) $ showsPrec 7 a . showString " `div` " . showsPrec 8 b
showBinOp d Mod   a b = showParen (d > 7) $ showsPrec 7 a . showString " `mod` " . showsPrec 8 b
showBinOp d FDiv  a b = showParen (d > 7) $ showsPrec 7 a . showString " / " . showsPrec 8 b
showBinOp d Min   a b = showParen (d > 10) $ showString "min " . showsPrec 10 a . showString " " . showsPrec 10 b
showBinOp d Max   a b = showParen (d > 10) $ showString "max " . showsPrec 10 a . showString " " . showsPrec 10 b
showBinOp d And   a b = showParen (d > 3) $ showsPrec 3 a . showString " && " . showsPrec 4 b
showBinOp d Or    a b = showParen (d > 2) $ showsPrec 2 a . showString " || " . showsPrec 3 b
showBinOp d Xor   a b = showParen (d > 5) $ showsPrec 5 a . showString " `xor` " . showsPrec 6 b
showBinOp d BAnd  a b = showParen (d > 7) $ showsPrec 7 a . showString " .&. " . showsPrec 8 b
showBinOp d BOr   a b = showParen (d > 5) $ showsPrec 5 a . showString " .|. " . showsPrec 6 b

showCompOp :: Show a => Int -> CompOp -> a -> a -> ShowS
showCompOp d EQU a b = showParen (d > 4) $ showsPrec 4 a . showString " == " . showsPrec 4 b
showCompOp d NEQ a b = showParen (d > 4) $ showsPrec 4 a . showString " /= " . showsPrec 4 b
showCompOp d GTH a b = showParen (d > 4) $ showsPrec 4 a . showString " > " . showsPrec 4 b
showCompOp d LTH a b = showParen (d > 4) $ showsPrec 4 a . showString " < " . showsPrec 4 b
showCompOp d GEQ a b = showParen (d > 4) $ showsPrec 4 a . showString " >= " . showsPrec 4 b
showCompOp d LEQ a b = showParen (d > 4) $ showsPrec 4 a . showString " <= " . showsPrec 4 b

