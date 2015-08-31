#!/usr/bin/env runghc

{-# LANGUAGE NoMonomorphismRestriction, TupleSections, DeriveDataTypeable #-}

-- run with circo -Tpdf > out.pdf

import SExprLexer as SExpr
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

{- Juniper Parsing -}

convertPos (Juniper.AlexPn _ line col) = newPos "<input>" line col

match pred = token (show . snd) (convertPos . fst) (testTok . snd)
  where testTok tt = if pred tt then Just tt else Nothing

stuff' = match $ \t -> case t of STUFF _ -> True; _ -> False
stuff = do STUFF s <- stuff'; return s

braceOpen = match $ \t -> case t of BRACE_OPEN -> True; _ -> False
braceClose = match $ \t -> case t of BRACE_CLOSE -> True; _ -> False
semi = match $ \t -> case t of SEMI -> True; _ -> False

{- S-Expr Parsing -}

convertPos' (SExpr.AlexPn _ line col) = newPos "<input>" line col

match' pred = token (show . snd) (convertPos' . fst) (testTok . snd)
  where testTok tt = if pred tt then Just tt else Nothing

atom' = match' $ \t -> case t of ATOM _ -> True; _ -> False
atom = do ATOM s <- atom'; return s

parenOpen = match' $ \t -> case t of PAREN_OPEN -> True; _ -> False
parenClose = match' $ \t -> case t of PAREN_CLOSE -> True; _ -> False

data SExpr = 
    Atom String
  | Expr [SExpr]
  deriving (Show, Eq, Data, Typeable)

atomSExpr = atom >>= return . Atom

exprSExpr = between parenOpen parenClose (many sexpr) >>= return . Expr

sexpr = (try atomSExpr) <|> exprSExpr

reportParseError :: Show a => Either ParseError a -> a
reportParseError (Left e) = error $ "Parse error\n" ++ show e
reportParseError (Right c) = c

parseSExpr :: FilePath -> String -> SExpr
parseSExpr file =
  reportParseError . parse sexpr file . SExpr.alexScanTokens

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

parseJuniper :: FilePath -> String -> JuniperConfig
parseJuniper file =
  JuniperConfig file . reportParseError . parse juniper file . Juniper.alexScanTokens

tag :: Command -> [String]
tag (Compound t _) = t
tag (Simple t) = t

{- Find interesting stuff in config -}

type Path = [String]
type CommandPath = (Path, Command)

isIPv4 :: String -> Bool
isIPv4 = isJust . matchRegex (mkRegex "[0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+")

commandPaths :: CommandPath -> [CommandPath]
commandPaths (path, cmd@(Simple _))          = [(path, cmd)]
commandPaths (path, cmd@(Compound tag cmds)) = 
	(path, cmd) : (commandPaths . (path++tag,) =<< cmds)

neighbor :: CommandPath -> Bool
neighbor ("protocols":"bgp":t , cmd) = (isPrefixOf ["neighbor"] . tag $ cmd) && (isIPv4 . last . tag $ cmd)
neighbor _ = False

localPreference :: CommandPath -> Bool
localPreference (_, cmd) = isPrefixOf ["local-preference"] . tag $ cmd

localAddress :: CommandPath -> Bool
localAddress ("protocols":"bgp":t , cmd) = (isPrefixOf ["local-address"] . tag $ cmd) && (isIPv4 . last . tag $ cmd)
-- k (_, cmd) = (isPrefixOf ["local-address"] . tag $ cmd) && (isIPv4 . last . tag $ cmd)
localAddress _ = False


-- http://www.juniper.net/techpubs/en_US/junos14.2/topics/concept/junos-cli-configuration-mode-overview.html
-- https://en.wikipedia.org/wiki/Create,_read,_update_and_delete
-- type ConfigChange = 
-- | create CommandPath
--   create CommandPath
--  update CommandPath
--  delete [String]

addCommand :: CommandPath -> Command -> Command
addCommand (l, c') c@(Compound tag cmds) =
  case stripPrefix tag l of
    Nothing -> c
    Just [] -> Compound tag $ cmds ++ [c']
    Just l' -> Compound tag $ map (addCommand (l', c')) cmds
addCommand _ c = c

apply :: [CommandPath] -> JuniperConfig -> JuniperConfig
apply [] jc = jc 
apply (cp:t) (JuniperConfig file c) = apply t $ JuniperConfig file (addCommand cp c)

-- local-address


{- BGP Configs -}

{- 
TODO, give more names to elements of the configuration
      and include their origin paths

data IP = String

data Neighbor = Neighbor {
  ip :: IP,
  preference :: String,
  command :: [CommandPath]
  path :: Path
}

data InternalRouter = InternalRouter {
  file :: String,
  name :: String,
  ip :: IP,
  neighbors :: [Neighbor]
  path :: Path
  command :: [CommandPath]
}

data BGPConfigs = BGPConfigs {
  routers :: [InternalRouter]
} deriving (Show, Eq)
-}

data BGPConfigs = BGPConfigs {
  names :: Map String String,
  neighbors :: Map String [(String,Int)]
} deriving (Show, Eq)

(<#>) :: (a->b)->(c->d)->(a,c)->(b,d)
f <#> g = \(x,y) -> (f x, g y)

headDefault :: a -> [a] -> a
headDefault x []    = x
headDefault _ (h:_) = h 

rootPath ::  Command -> CommandPath
rootPath = ([],)

bgpCommands :: JuniperConfig -> [CommandPath]
bgpCommands (JuniperConfig file cfg) =
  let paths = commandPaths $ rootPath cfg
      r  = head $ filter localAddress paths
      ns = filter neighbor paths
      ps = filter localPreference . commandPaths =<< ns
  in r : ns ++ ps

bgpConfigs :: [JuniperConfig] -> BGPConfigs
bgpConfigs = uncurry BGPConfigs . (fromList <#> fromList) . unzip . map bgpConfig
  where
    bgpConfig :: JuniperConfig -> ((String, String), (String, [(String,Int)]))
    bgpConfig (JuniperConfig file cfg) =
      let paths = commandPaths $ rootPath cfg
          r  = last . tag . snd . head $ filter localAddress paths   -- assert that they are all the same/there is only one
          ns = neighborConfig <$> filter neighbor paths
      in  ((r, file), (r, ns))
    neighborConfig :: CommandPath -> (String,Int)
    neighborConfig n = 
      let ip = last . tag . snd $ n
      	  paths = commandPaths n
      	  prefs = read . last . tag . snd <$> filter localPreference paths
      in (ip, headDefault 200 prefs)

-- TODO, rename String to IP

internalRouters :: BGPConfigs -> [String]
internalRouters (BGPConfigs _ bgp) = keys bgp

internalRouterNames :: BGPConfigs -> [(String,String)]
internalRouterNames (BGPConfigs names _) = assocs names

connections :: BGPConfigs -> [(String,String)]
connections (BGPConfigs _ bgp) = [(r,n) | (r,ns) <- assocs bgp, (n,_) <- ns]

preferences :: BGPConfigs -> [((String,String),Int)]
preferences (BGPConfigs _ bgp) = [((r,n),p) | (r,ns) <- assocs bgp, (n,p) <- ns]

possibleInternalConnections :: BGPConfigs -> [(String,String)]
possibleInternalConnections (BGPConfigs _ bgp) = (,) <$> keys bgp <*> keys bgp

isInternalConnection :: BGPConfigs -> (String,String) -> Bool
isInternalConnection (BGPConfigs _ bgp) (a,b) = a `member` bgp && b `member` bgp

isInternalNode :: BGPConfigs -> String -> Bool
isInternalNode (BGPConfigs _ bgp) n = n `member` bgp

{- testing -}
testConfig :: String -> String -> [(String,Int)] -> JuniperConfig
testConfig name r ns = JuniperConfig name $ Compound [] [
    Compound ["protocols"] [
      Compound ["bgp"] $ 
        Simple ["local-address", r] :
        map (\(n,pref) -> Compound ["neighbor", n] [Simple ["local-preference", show pref]]) ns
    ],
    Simple ["source-address", r]
  ]

tests :: IO ()
tests = do
  quickCheck $ \name r ns -> BGPConfigs (fromList [(r,name)]) (fromList [(r,ns)]) == 
                             bgpConfigs [testConfig name r ns]
  quickCheck $ isIPv4 "192.168.1.1"
  quickCheck $ not $ isIPv4 "2001:468:6::1"

{- visualize config -}

visualizeFullDot :: BGPConfigs -> String
visualizeFullDot cfg =
  let nodes = formatNode <$> internalRouterNames cfg
      edges = formatEdge <$> connections cfg
  in  formatGraph $ nodes ++ edges
  where
    formatEdge (a,b)  = format "\"{0}\" -> \"{1}\"{2}" [a, b, if isInternalConnection cfg (a,b)
    	                                                      then " [color=red]"
    	                                                      else ""]
    formatNode        = format "\"{0}\" [shape=box, label=\"{1} - {0}\"]" . toList
    formatGraph stmts = format "digraph G {{0}\n}\n" [("\n  "++) =<< stmts]

visualizeBigExternalDot :: BGPConfigs -> String
visualizeBigExternalDot cfg =
  let external    = [t | (_,t) <- connections cfg, not (isInternalNode cfg t)]
      bigExternal = external \\ nub external
      bigEdges    = [e | e <- connections cfg, snd e `elem` bigExternal]
  in  formatGraph $ formatEdges bigEdges ++ 
                    formatNodes (internalRouterNames cfg)
  where
    formatNodes       = map $ format "\"{0}\" [shape=box, label=\"{1} - {0}\"]" . toList
    formatEdges       = map $ format "\"{0}\" -> \"{1}\"" . toList
    formatGraph stmts = format "digraph G {{0}\n}\n" [("\n  "++) =<< stmts]

toList :: (a,a) -> [a]
toList (x,y) = [x,y]

visualizeCoreDot :: BGPConfigs -> String
visualizeCoreDot cfg =
  let allEdges     = possibleInternalConnections cfg
      actualEdges  = [e | e <- connections cfg, isInternalConnection cfg e]
      missingEdges = allEdges \\ actualEdges
  in  formatGraph $ formatEdges "black" actualEdges ++ 
                    formatEdges "red" missingEdges ++
                    formatNodes (internalRouterNames cfg)
  where
    formatNodes       = map $ format "\"{0}\" [shape=box, label=\"{1} - {0}\"]" . toList
    formatEdges clr   = map $ format "\"{1}\" -> \"{2}\" [color={0}]" . (clr:) . toList
    formatGraph stmts = format "digraph G {{0}\n}\n" [("\n  "++) =<< stmts]

visualizeCommandPaths :: [CommandPath] -> String
visualizeCommandPaths = concatMap ("\n"++) . map (intercalate " " . (\(path,cmd)-> path++tag cmd))

visualizeTokens :: String -> String
visualizeTokens = concatMap ("\n"++) . map (show . snd) . Juniper.alexScanTokens

visualizeConfig :: JuniperConfig -> String
visualizeConfig = rec "" . root
  where 
    rec indent (Simple tag) = format "{0}{1};\n" [indent, intercalate " " tag]
    rec indent (Compound tag cmds) = 
      let subs = rec ("  " ++ indent) <$> cmds
      in  format "{0}{1} {\n{2}{0}}\n" [indent, intercalate " " tag, concat subs]

commas :: (a -> a -> b) -> [a] -> [b]
commas _ [] = []
commas _ [x] = []
commas f (x:y:t) = f x y : commas f (y:t)

visualizeConstraints :: BGPConfigs -> String
visualizeConstraints bgp = 
  let eqCls    = groupBy ((==) <##> snd) . sortBy (compare <##> snd) . preferences $ bgp
      eqFormat = commas (\(x,_) (y,_)-> format "(< {0} {1})" [cost x, cost y]) $ map head eqCls
      ltFormat = commas (\(x,_) (y,_)-> format "(= {0} {1})" [cost x, cost y]) =<< eqCls
  in  intercalate "\n" $ eqFormat ++ ltFormat
  where
  	cost :: (String, String) -> String
  	cost = format "(cost \"{0}\" \"{1}\")" . toList
  	(<##>) :: (b -> b -> c) -> (a -> b) -> a -> a -> c
  	f <##> g = \x y-> f (g x) (g y)

visualizeSExpr :: SExpr -> String
visualizeSExpr (Atom a) = a
visualizeSExpr (Expr l) = format "({0})" [intercalate " " $ map visualizeSExpr l]

handle :: [FilePath] -> ([JuniperConfig] -> BGPConfigs -> String) -> IO String
handle files f = do
  raws <- sequence $ readFile <$> files
  let cfgs = uncurry parseJuniper <$> zip (takeBaseName <$> files) raws
  let bgp = bgpConfigs cfgs
  return (f cfgs bgp)

cmdlineUpdate :: String -> CommandPath
cmdlineUpdate s = 
  let l = splitOn " " s
      (path, tag) = splitAt (length l - 3) (init l)
  in  case last l of
      ";"  -> (path, Simple tag)
      "{}" -> (path, Compound tag [])


importlst :: CommandPath -> Bool
importlst ("protocols":"bgp":t , cmd) = (isPrefixOf ["import"] . tag $ cmd)
importlst _ = False

policy :: CommandPath -> Bool
policy ("policy-options":t, cmd) = (isPrefixOf ["policy-statement"] . tag $ cmd)
policy _ = False

prefix_list :: CommandPath -> Bool
prefix_list ("policy-options":t, cmd) = (isPrefixOf ["prefix-list"] . tag $ cmd)
prefix_list _ = False

get_policy_names :: Command -> [String]
get_policy_names (Simple (t:pols)) = filter (\p -> p /= "[" && p /= "]") pols
get_policy_names _ = []

policy_name (Compound ["policy-statement", name] _) = name
policy_name _ = ""

get_policy :: [CommandPath] -> String -> Command
get_policy pols name =
  (snd (head (filter (\path -> policy_name (snd path) == name) pols)))
                                  
contract :: [CommandPath] -> [CommandPath] -> CommandPath -> SExpr
contract policies prefix_lists path =
  let policy_names = get_policy_names (snd path) in
  let pols = map (get_policy policies) policy_names in
  traceShow pols $ Expr [Atom "HAHAHA"]

config_to_blowstick :: JuniperConfig -> SExpr
config_to_blowstick (JuniperConfig file cfg) =
  let paths = commandPaths $ rootPath cfg in
  let policies = filter policy paths in
  let prefix_lists = filter prefix_list paths in
  contract policies prefix_lists $ last $ filter importlst paths
      

blowstickify :: [JuniperConfig] -> String
blowstickify (jc : jcs) = visualizeSExpr (config_to_blowstick jc)
blowstickify [] = ""


help :: String
help = format (unlines [
  "Usage: {0} COMMAND",
  "",
  "The most commonly used {0} commands are:",
  "",
  "   project FILE...          Project BGP relevant parts of the Juniper ",
  "                            configurations contained in FILEs.",
  "",
  "   infer topology FILE...   Infer the topology of the Juniper configurations ",
  "                            contained in FILEs. Use dot to visualize the output",
  "                            (requires an installation of graphviz).",
  "",
  "   infer contracts FILE...  Infer the contracts of the Juniper configurations ",
  "                            contained in FILEs.",
  "",
  "   inject add FILE STMT...  Inject statements into the Juniper configuration ",
  "                            contained in FILE. The statements are provided by ",
  "                            STMTs. Each STMT is a juniper statement, appended ",
  "                            with ' {}' for container statements, and ' ;' for ",
  "                            leaf statements. e.g.",
  "                              inject add F \"protocols bgp neighbor a.b.c.d {}\"",
  "                              adds a new neighbor to the Juniper configuration ",
  "                              contained in the file F.",
  "",
  "   help                     Display this help message and exit."]) ["bagpipe"]

cmdline :: [String] -> IO String
cmdline ("project":files) = handle files (\jcs _-> visualizeCommandPaths . bgpCommands =<< jcs)
cmdline ("infer":"topology":files) = handle files (\_ bgp-> visualizeFullDot bgp)
cmdline ("infer":"contracts":files) = handle files (\_ bgp-> visualizeConstraints bgp)
cmdline ("inject":"add":file:cmds) = handle [file] (\[jc] _->
  visualizeConfig $ apply (map cmdlineUpdate cmds) jc)
cmdline ["sexpr", file] = readFile file >>= return . visualizeSExpr . parseSExpr file
cmdline ("blowstick":files) = handle files (\jcs _ -> blowstickify jcs)
cmdline _ = return help

main :: IO ()
main = do
--  tests
  args <- getArgs
  out <- cmdline args
  putStrLn out
