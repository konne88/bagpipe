{
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module SExprLexer (Token(..), PosToken, AlexPosn(..), alexScanTokens) where

import Data.Data

}

%wrapper "posn"

$space = $white # \n
$atom = [^ $space \( \) \; ] 

tokens :-

";" .*          ;
"("             { out $ const PAREN_OPEN }
")"             { out $ const PAREN_CLOSE }
$atom+          { out $ ATOM }
$white+         ;

{

data Token = 
    ATOM String
  | PAREN_OPEN
  | PAREN_CLOSE
  deriving (Show, Data, Typeable)

type PosToken = (AlexPosn, Token)

deriving instance Typeable AlexPosn
deriving instance Data AlexPosn

out f p s = (p, f s)
}
