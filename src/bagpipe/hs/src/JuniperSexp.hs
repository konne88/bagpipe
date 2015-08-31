#!/usr/bin/env runghc

{-# LANGUAGE NoMonomorphismRestriction, TupleSections, DeriveDataTypeable, OverloadedStrings #-}

import JuniperLexer as Juniper
import Prelude hiding (lookup)
import Control.Arrow
import Control.Monad
import Control.Applicative hiding (many, (<|>))
import Data.Either
import Data.List hiding (lookup)
import Data.Maybe
import Text.Parsec
import qualified Text.Parsec.Token as P
import Text.Parsec.Pos (newPos)
import Text.Format
import System.Environment
import Data.Map.Strict hiding (map, toList, lookup, filter, (\\))
import Data.Either.Utils
import Debug.Trace
import Test.QuickCheck
import Data.Generics (Data, Typeable, mkQ, mkT, everything, everywhere)
import System.FilePath.Posix
import Text.Regex
import Data.List.Split
import Data.Sexp
import Language.Sexp.Printer
import Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString.Lazy.Char8 as C


{- Juniper Parsing -}

convertPos (Juniper.AlexPn _ line col) = newPos "<input>" line col

match pred = token (show . snd) (convertPos . fst) (testTok . snd)
  where testTok tt = if pred tt then Just tt else Nothing

stuff' = match $ \t -> case t of STUFF _ -> True; _ -> False
stuff = do STUFF s <- stuff'; return s

braceOpen = match $ \t -> case t of BRACE_OPEN -> True; _ -> False
braceClose = match $ \t -> case t of BRACE_CLOSE -> True; _ -> False
semi = match $ \t -> case t of SEMI -> True; _ -> False

reportParseError :: Show a => Either ParseError a -> a
reportParseError (Left e) = error $ "Parse error\n" ++ show e
reportParseError (Right c) = c

{- Another way of representing this would be

data Command = Command (Map [String] Command)

-}

-- http://www.juniper.net/techpubs/en_US/junos14.2/topics/concept/junos-cli-operational-configuration-modes-overview.html
data Command =
    Compound [String] [Command]  -- Container
  | Simple [String]              -- Leaf
  deriving (Show, Eq, Data, Typeable)

data JuniperConfig = JuniperConfig {file::FilePath, root::Command} deriving (Show,Eq)

braces = between braceOpen braceClose

commandEx = do 
  r <- many stuff
  b <- braces $ many command
  return $ Compound r b

commandSimpl = do
  r <- many1 stuff
  semi
  return $ Simple r

command = (try commandSimpl) <|> commandEx

juniper = do
  cmds <- many command
  eof
  return $ Compound [] cmds

parseJuniper :: FilePath -> String -> Command
parseJuniper file =
  reportParseError . parse juniper file . Juniper.alexScanTokens

juniperToSexp :: Command -> Sexp
juniperToSexp (Compound s c) = List $ (map (Atom . C.pack) s) ++ [List (map juniperToSexp c)]
juniperToSexp (Simple s) = List $ map (Atom . C.pack) s

cmdline :: [String] -> IO ByteString
cmdline [file] = readFile file >>= return . printHum . juniperToSexp . parseJuniper file

main :: IO ()
main = do
--  tests
  args <- getArgs
  out <- cmdline args
  C.putStrLn out
