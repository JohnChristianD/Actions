module Main where

import Control.Monad (forM_)
import Data.List (intercalate)
import System.Directory (createDirectoryIfMissing)
import System.Environment (lookupEnv)

-- The generator is intentionally a proposition emitter, not a proof oracle.
-- Each row is: module | file | imports(; separated) | proposition | proof term
-- A row can be added without recompiling this generator.
data Candidate = Candidate
  { moduleName :: String
  , fileStem :: String
  , imports :: [String]
  , proposition :: String
  , proofTerm :: String
  }

splitOn :: Char -> String -> [String]
splitOn sep = go
  where
    go [] = [""]
    go (c:cs)
      | c == sep = "" : go cs
      | otherwise =
          let (x:xs) = go cs
          in (c:x) : xs

trim :: String -> String
trim = f . f
  where
    f = reverse . dropWhile (== ' ')

parseCandidate :: String -> Maybe Candidate
parseCandidate raw
  | null line = Nothing
  | head line == '#' = Nothing
  | otherwise =
      case splitOn '|' line of
        [m, s, imps, prop, proof] ->
          Just
            Candidate
              { moduleName = trim m
              , fileStem = trim s
              , imports = map trim (splitOn ';' imps)
              , proposition = trim prop
              , proofTerm = trim proof
              }
        _ -> error ("invalid discovery grammar row: " ++ line)
  where
    line = trim raw

loadCandidates :: FilePath -> IO [Candidate]
loadCandidates path = do
  text <- readFile path
  pure [c | Just c <- map parseCandidate (lines text)]

sourceFor :: Candidate -> String
sourceFor c =
  "{-# OPTIONS --safe #-}\n"
  ++ "module " ++ moduleName c ++ " where\n\n"
  ++ "open import Agda.Builtin.Equality using (_≡_; refl)\n"
  ++ "open import Data.Product using (_×_; _,_)\n"
  ++ "open import Exotic.efficient_chad.Int8 using (Int8; int8OfNat; one8; zero8)\n"
  ++ intercalate "\n" (imports c)
  ++ "\n\n"
  ++ "candidate : " ++ proposition c ++ "\n"
  ++ "candidate = " ++ proofTerm c ++ "\n"

main :: IO ()
main = do
  configured <- lookupEnv "DISCOVERY_GRAMMAR"
  let grammar = maybe ".ci/discovery/grammar.tsv" id configured
      root = ".ci/generated-conjectures"
  candidates <- loadCandidates grammar
  createDirectoryIfMissing True root
  forM_ candidates $ \c ->
    writeFile (root ++ "/" ++ fileStem c ++ ".agda") (sourceFor c)
