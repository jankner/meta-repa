{-# LANGUAGE QuasiQuotes, TemplateHaskell #-}
module StencilExp where

import Language.LBNF.Compiletime

import Language.LBNF(lbnf, dumpCode, bnfc)

bnfc [lbnf|

StencilE. StencilE ::= [Line] ;

Line. Line ::= [SExpr] ;

ECond.   SExpr0 ::= SExpr1 "?" SExpr ":" SExpr ;
EOr.     SExpr1 ::= SExpr2 "||" SExpr1 ;
EAnd.    SExpr2 ::= SExpr3 "&&" SExpr2 ;
ELt.     SExpr3 ::= SExpr4 "<"  SExpr4 ;
ELtE.    SExpr3 ::= SExpr4 "<=" SExpr4 ;
EGt.     SExpr3 ::= SExpr4 ">"  SExpr4 ;
EGtE.    SExpr3 ::= SExpr4 ">=" SExpr4 ;
EEq.     SExpr3 ::= SExpr4 "==" SExpr4 ;
ENEq.    SExpr3 ::= SExpr4 "/=" SExpr4 ;
EPlus.   SExpr4 ::= SExpr4 "+"  SExpr5 ;
EMinus.  SExpr4 ::= SExpr4 "-"  SExpr5 ;
EMult.   SExpr5 ::= SExpr5 "*"  SExpr6 ;
EDiv.    SExpr5 ::= SExpr5 "/"  SExpr6 ;
ENeg.    SExpr6 ::= "-" SExpr7 ;
EVar.    SExpr7 ::= Ident ;
EInt.    SExpr7 ::= Integer ;
EDouble. SExpr7 ::= Double ;

separator nonempty SExpr "," ;
separator Line ";" ;

_.  SExpr   ::= SExpr0 ;
_.  SExpr0  ::= SExpr1 ;
_.  SExpr1  ::= SExpr2 ;
_.  SExpr2  ::= SExpr3 ;
_.  SExpr3  ::= SExpr4 ;
_.  SExpr4  ::= SExpr5 ;
_.  SExpr5  ::= SExpr6 ;
_.  SExpr6  ::= SExpr7 ;
_.  SExpr7  ::= "(" SExpr ")" ;

entrypoints StencilE ;

|]
