{
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving #-}

module JuniperLexer (Token(..), PosToken, AlexPosn(..), alexScanTokens) where

import Data.Data

}

%wrapper "posn"

@int = [0-9\-][0-9]*
$wordchar = [a-zA-Z0-9_]
$wordstart = [a-zA-Z_]
@word = $wordstart $wordchar*
$space = $white # \n
$stuff = [ a-z A-Z 0-9 \_ \- \. \: \/ \* \[ \] \| \> \< \( \) \& ]

$stringpart = . # \"

tokens :-

\" $stringpart+ \"  { out $ STUFF }
"/*" .*         ;
"#" .*          ;
"{"             { out $ const BRACE_OPEN }
"}"             { out $ const BRACE_CLOSE }
";"             { out $ const SEMI }
$stuff+         { out $ STUFF }
$white+         ;

{

data Token = 
    SEMI
  | BRACE_OPEN
  | BRACE_CLOSE
  | STUFF String
  deriving (Show, Data, Typeable)

type PosToken = (AlexPosn, Token)

deriving instance Typeable AlexPosn
deriving instance Data AlexPosn

out f p s = (p, f s)
}
