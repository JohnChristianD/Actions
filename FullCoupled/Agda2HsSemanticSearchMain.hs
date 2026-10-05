{-# LANGUAGE FlexibleContexts, NoMonomorphismRestriction, TemplateHaskell #-}

module Main where

import Plugin.InversionPlugin
import FullCoupled.Agda2HsSemanticSearch

splits :: (Argument [String], Result [String]) => [String] -> [([String], [String])]
splits = $(inv 'pathAppend)

main :: IO ()
main = do
  let plan = canonicalPlan
      inverted = splits splitTarget
      complete = canonicalSearchComplete
      nontrivial = canonicalPlanNontrivial
  putStrLn semanticSearchReport
  print plan
  print inverted
  print complete
  print nontrivial
