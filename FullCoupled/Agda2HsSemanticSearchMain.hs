{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction, TemplateHaskell #-}

module Main where

import Data.List (dropWhile, dropWhileEnd, isInfixOf, isPrefixOf)
import Plugin.InversionPlugin
import FullCoupled.Agda2HsSemanticSearch
import FullCoupled.Agda2HsTheoremGraphEGraph
import System.Environment (getArgs)

graphEdgeCount :: String -> Int
graphEdgeCount source =
  length
    [ line
    | line <- lines source
    , "->" `isInfixOf` line
    ]

breakOn :: String -> String -> Maybe (String, String)
breakOn needle = go []
  where
    go _ [] = Nothing
    go prefix remaining
      | needle `isPrefixOf` remaining =
          Just (reverse prefix, drop (length needle) remaining)
      | otherwise =
          case remaining of
            [] -> Nothing
            (c : cs) -> go (c : prefix) cs

dotTrim :: String -> String
dotTrim =
  dropWhile isDotSpace
    . dropWhileEnd isDotSpace

isDotSpace :: Char -> Bool
isDotSpace c =
  c == ' '
    || c == '\t'
    || c == '\r'
    || c == '\n'
    || c == '"'
    || c == ';'

dotNodeToken :: String -> String
dotNodeToken =
  takeWhile
    (\c -> c /= ' ' && c /= '\t' && c /= '\r' && c /= '\n' && c /= '[' && c /= ';')
    . dotTrim

parseDotEdge :: String -> Maybe (String, String)
parseDotEdge line = do
  (left, right) <- breakOn "->" line
  let source = dotNodeToken left
      target = dotNodeToken right
  if null source || null target
    then Nothing
    else Just (source, target)

graphEdges :: String -> [(String, String)]
graphEdges source =
  [ edge
  | line <- lines source
  , "->" `isInfixOf` line
  , Just edge <- [parseDotEdge line]
  ]

theoremGraphSummary :: FilePath -> IO (String, [(String, String)])
theoremGraphSummary path = do
  source <- readFile path
  let edges = graphEdges source
      autonomous = autonomousGraphSearchCount edges
  pure
    ( "theorem-graph-edges=" ++ show (graphEdgeCount source)
        ++ " autonomous-a-star-chains="
        ++ show autonomous
    , edges
    )

splits :: (Argument [String], Result [String]) => [String] -> [([String], [String])]
splits = $(inv 'pathAppend)

main :: IO ()
main = do
  args <- getArgs
  graphPath <-
    case args of
      [path] -> pure path
      _ -> fail "expected TheoremsMonolith dependency-graph DOT path"

  (graphSummary, edges) <- theoremGraphSummary graphPath
  let plan = canonicalPlan
      inverted = splits splitTarget
      complete = canonicalSearchComplete
      nontrivial = canonicalPlanNontrivial
      egraphComplete = symbolicEGraphRegression
      egraphAssociative = eGraphAssociativityRegression
      autonomousReport = autonomousGraphSearchReport edges

  putStrLn semanticSearchReport
  putStrLn graphSummary
  putStrLn autonomousReport
  print plan
  print inverted
  print complete
  print nontrivial
  print egraphComplete
  print egraphAssociative
