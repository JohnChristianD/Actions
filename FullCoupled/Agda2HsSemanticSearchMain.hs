{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction, TemplateHaskell #-}

module Main where

import Data.List (isInfixOf)
import Plugin.InversionPlugin
import FullCoupled.Agda2HsSemanticSearch
import System.Environment (getArgs)

graphEdgeCount : String -> Int
graphEdgeCount source =
  length
    [ line
    | line <- lines source
    , "->" `isInfixOf` line
    ]

theoremGraphSummary :: FilePath -> IO String
theoremGraphSummary path = do
  source <- readFile path
  pure ("theorem-graph-edges=" ++ show (graphEdgeCount source))

splits :: (Argument [String], Result [String]) => [String] -> [([String], [String])]
splits = $(inv 'pathAppend)

main :: IO ()
main = do
  args <- getArgs
  graphPath <-
    case args of
      [path] -> pure path
      _ -> fail "expected TheoremsMonolith dependency-graph DOT path"

  graphSummary <- theoremGraphSummary graphPath
  let plan = canonicalPlan
      inverted = splits splitTarget
      complete = canonicalSearchComplete
      nontrivial = canonicalPlanNontrivial

  putStrLn semanticSearchReport
  putStrLn graphSummary
  print plan
  print inverted
  print complete
  print nontrivial
