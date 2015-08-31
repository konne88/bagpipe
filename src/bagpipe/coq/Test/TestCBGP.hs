#!/usr/bin/env runghc

{-# LANGUAGE StandaloneDeriving #-}
import MessageHandling
import Text.Printf
import Text.ParserCombinators.Parsec
import System.Process
import Data.Functor
import Data.Maybe
import Data.List
import Control.Monad.Trans.Either
import Control.Monad.Trans.Maybe
import Control.Monad.Trans
import Control.Monad
import System.Exit

import Test.QuickCheck
import Test.QuickCheck.Gen
import Test.QuickCheck.Monadic (assert, monadicIO, run)

type IP = String
type CIDR = String
type ASN = Int

--deriving instance Show PolicyResult
deriving instance Show BGPPathAttributes
deriving instance Show TraceError
deriving instance Show Event
deriving instance Show Setup
deriving instance Show Match
deriving instance Show Modify
deriving instance Show Action
-- deriving instance Show Rule

ignore :: Parser b -> a -> Parser a
ignore p a = p >> return a

eol :: Parser ()
eol = (string "\n" <|> string "\r\n") >> return ()

decimal :: Parser Int
decimal = read <$> many1 digit

ip :: Int -> Int -> Int -> Int -> IP
ip a b c d = printf "%d.%d.%d.%d" a b c d

parseIP :: Parser IP
parseIP = do
  a <- decimal
  char '.'
  b <- decimal
  char '.'
  c <- decimal
  char '.'
  d <- decimal
  return $ ip a b c d

cidr :: IP -> Int -> CIDR
cidr ip mask = printf "%s/%d" ip mask

parseCIDR :: Parser CIDR
parseCIDR = do
  ip <- parseIP
  char '/'
  mask <- decimal
  return $ cidr ip mask

parsePath :: Parser [ASN]
parsePath =
  (string "null" >> return []) <|> decimal `sepBy1` char ' '

-- described here:
-- http://c-bgp.sourceforge.net/doc/html/nodes/bgp_router_show_rib.html
parseAnnouncement :: Parser (Maybe (CIDR, BGPPathAttributes))
parseAnnouncement = parseNA <|> parseA
  where
    parseNA :: Parser (Maybe (CIDR, BGPPathAttributes))
    parseNA = do
      string "(null)"
      return Nothing
    parseA :: Parser (Maybe (CIDR, BGPPathAttributes))
    parseA = do
      char '*' <|> char 'i'
      char '>' <|> char ' '
      char ' '
      nlri <- parseCIDR
      char '\t'
      parseIP
      char '\t'
      pref <- decimal
      char '\t'
      decimal
      char '\t'
      path <- parsePath
      char '\t'
      char 'i'
      -- CBGP's trace doesn't contain the communities
      return . Just $ (nlri, Build_BGPPathAttributes pref [] path)

parseASN :: Parser ASN
parseASN = decimal

parseRouter :: Parser (ASN, IP)
parseRouter = do
  string "AS"
  as <- parseASN
  char ':'
  r <- parseIP
  return (as, r)
  
parseMode :: Parser Mode
parseMode = do
  m  <- string "INT" <|> string "EXT"
  string " --> "
  m' <- string "INT" <|> string "EXT"
  return $ if m == "INT" && m' == "INT" then Ibgp else Ebgp

-- policyResultParser :: Parser PolicyResult
-- policyResultParser = try iBGPFilter <|> try ssldFilter <|> try srcFilter <|> fwdFilter
--   where

--     iBGPFilter = string "out-filtered(iBGP-peer --> iBGP-peer)" >> eol >> 
--                  string "\tfiltered" >> eol >> return Filtered

--     ssldFilter = string "out-filtered(ssld)" >> eol >> 
--                  string "\tfiltered" >> eol >> return Filtered

--     srcFilter = string "out-filtered(next-hop-peer)" >> eol >> 
--                 string "\tfiltered" >> eol >> return Filtered

--     fwdFilter = string "announce_route to " >> parseRouter >> eol >> 
--                 string "\treplaced" >> eol >> return Replaced



-- That up there? It's a smart parser. Instead, let's use a dumb parser.

policyResultParser :: Parser PolicyResult
policyResultParser = try filtered <|> replaced
  where
    filtered = manyTill anyChar eol >>
               string "\tfiltered" >> eol >>
               optional (string "\texplicit-withdraw" >> eol) >>
               return Filtered
    replaced = manyTill anyChar eol >>
               string "\treplaced" >> eol >> return Replaced

parseDisseminate :: Parser ((ASN, IP), PolicyResult)
parseDisseminate = do
  string "DISSEMINATE (" >> parseCIDR >> string ") from " >> parseRouter >> string " to "
  (as, r) <- parseRouter
  eol
  string "advertise_to_peer (" >> parseCIDR >> string ") from " >> parseRouter
  string " to " >> parseRouter >> string " (" >> parseMode >> char ')' >> eol
  res <- policyResultParser  
  return ((as, r), res)

parseRule :: Parser String
parseRule =
  try (string "Lowest ORIGIN") <|>
  try (string "Lowest MED") <|>
  string "Lowest ROUTER-ID" <|>
  string "Highest LOCAL-PREF" <|> 
  string "Shortest AS-PATH" <|>
  string "eBGP over iBGP" <|>
  string "Nearest NEXT-HOP"

parseMessage :: Parser (Maybe (CIDR, BGPPathAttributes))
parseMessage =
  try parseUpdate <|> parseWithdraw
  where
    parseUpdate = do
      string "BGP_MSG_RCVD: UPDATE" >> eol
      string "BGP_FSM_STATE: ESTABLISHED" >> eol
      string "\tupdate: " 
      parseAnnouncement

    parseWithdraw = do
      string "BGP_MSG_RCVD: WITHDRAW" >> eol
      string "BGP_FSM_STATE: ESTABLISHED"
      return Nothing

parseDecisionProcess :: Parser (Maybe CIDR)
parseDecisionProcess = do
  string "-------------------------------------------------------------------------------" >> eol
  string "DECISION PROCESS for "
  nlri <- parseCIDR 
  string " in " >> parseRouter >> eol
  string "\told-best: "
  oldal <- parseAnnouncement 
  eol
  ins <- many . try $ string "\teligible: " >> parseAnnouncement >>= ignore eol
  many $ string "rule: [ " >> parseRule >>= ignore (string " ]") >>= ignore eol
  string "\tnew-best: " 
  al <- parseAnnouncement
  eol
  -- optional explanation
  optional ((try (string "different NEXT-HOP") <|> try (string "different LOCAL-PREFs") <|> try (string "different COMMUNITIES") <|> string "different AS-PATHs" ) >>= ignore eol)
  string "\t*** "
  string "NEW BEST ROUTE" <|> string "BEST ROUTE UNCHANGED" <|> string "UPDATED BEST ROUTE" <|> string "NO BEST ROUTE"
  string " ***" >> eol
  dissems <- many $ parseDisseminate
  string "-------------------------------------------------------------------------------" >> eol
  many $ string "\tremove: " >> parseAnnouncement >> eol
  return $ Just nlri

parseDecision :: Parser (Maybe CIDR)
parseDecision = do
  try parseDecisionProcess <|> return Nothing
  
parseEvent :: Parser Event
parseEvent = do
  string "=====<<< EVENT "
  e <- decimal
  char '.' >> decimal >> string " >>>=====" >> eol
  string "HANDLE_MESSAGE from "
  r' <- parseRouter
  string " in "
  r  <- parseRouter
  eol
  ai <- parseMessage
  eol
  nlri <- parseDecision
  case (nlri, ai) of
    (Just p, Just (_, a)) -> eol >> (return $ Build_Event e r' r (Just p) (Just a))
    (_, Just (p, a)) -> (string "in-filtered(filter)" >> eol >> eol >>
                        (return $ Build_Event e r' r (Just p) (Just a)))
    (Just p, _) -> eol >> (return $ Build_Event e r' r (Just p) Nothing)
    _ -> eol >> (return $ Build_Event e r' r Nothing Nothing)

parseCBGPTrace :: String -> Either ParseError [Event]
parseCBGPTrace s =
   parse (many parseEvent >>= ignore eof) "" s

cbgpConfig :: Setup -> String
cbgpConfig setup = unlines $
  createASes ++ createExternalLinks ++
  [ printf "sim run" ] ++
  createInjections ++
  [ printf "sim options log-level everything",
    printf "sim run"]
  where
    createASes :: [String]
    createASes = do
      (as, rs) <- ases setup
      id 
        [ printf "net add domain %d igp" as ] ++ 
        createRouters as rs ++
        createInternalLinks rs ++
        [ printf "net domain %d compute" as,
          printf "bgp domain %d full-mesh" as]
    createRouters :: ASN -> [IP] -> [String]
    createRouters as rs = do
      r <- rs
      [ printf "net add node %s" r,
        printf "net node %s domain %d" r as,
        printf "bgp add router %d %s" as r]
    createInternalLinks :: [IP] -> [String]
    createInternalLinks rs = do
      r <- rs
      r' <- rs
      if r >= r' then [] else 
        [ printf "net add link %s %s" r r',
          printf "net link %s %s igp-weight --bidir 1" r r']
    createExternalLinks :: [String]
    createExternalLinks = do
      (pref, ((((as, r), i1), e1), (((as', r'), i2), e2))) <- zip [0,2..] $ links setup
      [ printf "net add link %s %s" r r' ] ++ 
        createExternalBGPConfig pref r  r' i1 e1 as' ++
        createExternalBGPConfig (pref + 1) r' r i2 e2 as
    createExternalBGPConfig :: Int -> IP -> IP -> [Rule] -> [Rule] -> ASN -> [String]
    createExternalBGPConfig pref r r' i e as' =
      [ printf "net node %s route add --oif=%s %s/32 1" r r' r',
        printf "bgp router %s" r,
        printf "  add peer %d %s" as' r',
        printf "  peer %s next-hop-self" r',
        printf "  peer %s filter in add-rule action \"local-pref %d\"" r' (pref + 100)] ++
      map (\ s -> printf "  peer %s filter in %s" r' s) (cbgpRules i) ++
      map (\ s -> printf "  peer %s filter out %s" r' s) (cbgpRules e) ++
      [printf "  peer %s up" r',
       printf "  exit" ]
    createInjections :: [String]
    createInjections = do
      ((_,r),p) <- injections setup
      [ printf "bgp router %s add network %s" r p ]

cbgpMatch :: Match -> String
cbgpMatch RAny = "any"
cbgpMatch (RNot m) = printf "! (%s)" (cbgpMatch m)
cbgpMatch (RAnd m1 m2) = printf "(%s & %s)" (cbgpMatch m1) (cbgpMatch m2)
cbgpMatch (ROr m1 m2) = printf "(%s | %s)" (cbgpMatch m1) (cbgpMatch m2)
cbgpMatch (RCommunityIs c) = printf "community is %d" c

cbgpAction :: Action -> String
cbgpAction AAccept = "accept"
cbgpAction AReject = "deny"
cbgpAction (AModify (MAddCommunity c)) = printf "community add %d" c
cbgpAction (AModify MStripCommunities) = "community strip"

cbgpRules :: [Rule] -> [String]
cbgpRules = map (\ (m, a) -> printf "add-rule\n    match \"%s\"\n    action \"%s\"\n    exit" (cbgpMatch m) (cbgpAction a))

-- based on http://c-bgp.sourceforge.net/tutorial.php
-- testSetup :: Setup
-- testSetup = Build_Setup
--   [(1, ["1.0.0.1", "1.0.0.2", "1.0.0.3"]),
--    (2, ["2.0.0.1", "2.0.0.2", "2.0.0.3"]),
--    (3, ["3.0.0.1"])]
--   [((1, "1.0.0.1"), (2, "2.0.0.1")), ((1, "1.0.0.2"), (2, "2.0.0.2")),
--    ((2, "2.0.0.3"), (3, "3.0.0.1"))]
--   [((1, "1.0.0.1"), "11.0.0.0/24")]

genASIP :: Int -> Gen String
genASIP as = do
  x1 <- choose (0, 255)
  x2 <- choose (0, 255)
  x3 <- choose (0, 255)
  return $ ip as x1 x2 x3

genCommunity :: Gen Int
genCommunity = do
  Positive c <- arbitrary
  return c

genAS :: Int -> Gen (Int, [String])
genAS as = do
  x <- listOf1 (genASIP as)
  return $ (as, nub x)

genASes :: Gen [(Int, [String])]
genASes = do
  Positive numASes <- (arbitrary :: Gen (Positive Int)) `suchThat` (\ x -> (getPositive x) <= 255)
  sequence $ map genAS [1 .. numASes + 1]

genRouter :: [(Int, [String])] -> Int -> Gen (Int, String)
genRouter ases as = do
  ip <- elements $ snd $ ases !! (as - 1)
  return $ (as, ip)

genLink' :: [(Int, [String])] -> Int -> Int -> Gen ((Int, String), (Int, String))
genLink' ases as1 as2 = do
  r1 <- genRouter ases as1
  r2 <- genRouter ases as2
  return $ (r1, r2)

genLink :: [(Int, [String])] -> Gen ((Int, String), (Int, String))
genLink ases = do
  as1 <- choose (1, length ases - 1)
  as2 <- choose (as1 + 1, length ases)
  genLink' ases as1 as2

type LinkWithRules = ((((Int, String), [Rule]), [Rule]), (((Int, String), [Rule]), [Rule]))


genMatch :: Int -> Gen Match
genMatch 0 = oneof [liftM RCommunityIs genCommunity, return RAny]
genMatch n | n>0 = 
	oneof [liftM RCommunityIs genCommunity,
               return RAny,
               -- liftM RNot sub,
               liftM2 RAnd sub sub,
               liftM2 ROr sub sub]
  where sub = genMatch (n `div` 2)

instance Arbitrary Match where
  arbitrary = sized genMatch

instance Arbitrary Action where
  arbitrary = oneof [return AAccept, return AReject,
                     return (AModify MStripCommunities),
                     liftM (AModify . MAddCommunity) genCommunity]

genRule :: Gen Rule
genRule = do
  m <- arbitrary
  ac <- arbitrary
  return (m, ac)

genRules :: Gen [Rule]
genRules = listOf1 genRule

genLinkWithRules :: [(Int, [String])] -> Gen LinkWithRules
genLinkWithRules ases = do
  (l1, l2) <- genLink ases
  i1 <- genRules
  e1 <- genRules
  i2 <- genRules
  e2 <- genRules
  return $ (((l1, i1), e1), ((l2, i2), e2))

nubByKey :: Eq b => (a -> b) -> [a] -> [a]
nubByKey f l = nubBy (\ x y -> f x == f y) l
  

genLinks :: [(Int, [String])] -> Gen [LinkWithRules]
genLinks ases = do
   links <- listOf1 $ genLinkWithRules ases
   return $ nubByKey linkWithoutRules links

genIP :: Gen String
genIP = do
  as <- choose (0, 255)
  genASIP as

genSubnet :: Gen String
genSubnet = do
  ip <- genIP
  sub <- (choose (1, 32) :: Gen Int)
  return $ ip ++ "/" ++ (show sub)

genAnnouncement :: [(Int, [String])] -> Gen ((Int, String), String)
genAnnouncement ases = do
  as <- choose (1, length ases - 1)
  router <- genRouter ases as
  subnet <- genSubnet
  return $ (router, subnet)

genAnnouncements ases = do
  anns <- listOf1 $ genAnnouncement ases
  return $ nub anns

smallerSubSequences :: Eq a => [a] => [[a]]
smallerSubSequences l =
  filter (\x -> x /= l) (subsequences l)
  
instance Arbitrary Setup where
  arbitrary = do
    ases <- genASes
    links <- genLinks ases
    announcements <- genAnnouncements ases
    return $ Build_Setup ases links announcements
  --shrink (Build_Setup ases links announcements) =
    --map (\links' -> Build_Setup ases links' announcements) (smallerSubSequences links)
    
-- configs


third :: (a,b,c) -> c
third (_,_,c) = c

applyInjections :: Setup -> [((ASN, IP), CIDR)] -> TraceExists -> EitherT TraceError IO TraceExists
applyInjections _ [] ns = return ns
applyInjections setup (i:is) ns = do
  -- liftIO . putStrLn . unlines $ show <$> debugTraceExists setup ns
  -- liftIO $ printf "injecting: %s\n" (show i)
  ns' <- hoistEither $ applyInjection setup i ns
  applyInjections setup is ns'

applyEvents :: Setup -> [Event] -> TraceExists -> EitherT TraceError IO TraceExists
applyEvents _ [] ns = return ns
applyEvents setup (e:es) ns = do
  --liftIO . putStrLn . unlines $ show <$> debugTraceExists setup ns
  --liftIO $ printf "event:     %s\n" (show e)
  ns' <- hoistEither $ applyEvent setup e ns
  applyEvents setup es ns'

checkEvents :: Setup -> [Event] -> EitherT TraceError IO TraceExists
checkEvents setup es =
  return (emptyNetwork setup) >>=
  applyInjections setup (injections setup) >>=
  applyEvents setup es
  -- assert that the network is now empty

checkSetup :: Setup -> IO (Maybe TraceError)
checkSetup setup = do
  config <- return $ cbgpConfig setup
  (_, _, trace) <- readProcessWithExitCode "cbgp" [] config
  e <- return $ parseCBGPTrace trace
  case e of
      Left err -> error $ printf "parse error on config %s" (show setup)
      Right events -> do
          result <- runEitherT $ checkEvents setup events
          return $ either Just (Prelude.const Nothing) result

empty :: Maybe a -> Bool
empty Nothing = True
empty (Just _) = False

verifyReturnsNothing :: Setup -> Property
verifyReturnsNothing setup = monadicIO $ do
  run $ putStrLn $ show setup
  error <- run $ checkSetup setup
  assert $ empty error

verify :: Setup -> IO ()
verify setup = do
  config <- return $ cbgpConfig setup
  (_, _, trace) <- readProcessWithExitCode "cbgp" [] config
  printf trace
  e <- return $ parseCBGPTrace trace
  case e of
      Left err -> error $ printf "parse error on config %s\n\n\n%s" (show setup) (show err)
      Right events -> do
        result <- runEitherT $ checkEvents setup events
        printf "error:     %s\n" $ show $ either Just (Prelude.const Nothing) result

test :: Setup -> IO Bool
test setup = do
  result <- checkSetup setup
  --now <- getCurrentTime
  case result of
    Nothing -> putStrLn $ printf "SUCCESS"
    Just e -> putStrLn $ printf "FAILURE on config %s" $ show setup
  return $ empty result

main :: IO ()
main = do
  setup <- generate (resize 8 arbitrary)
  result <- test setup
  if result
    then exitSuccess
    else exitFailure
