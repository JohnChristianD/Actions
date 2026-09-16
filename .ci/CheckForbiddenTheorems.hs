module Main where

import Control.Monad (forM_)
import Data.List (isInfixOf)
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath ((</>))

forbidden :: [String]
forbidden =
  [ "transcendental"
  , "transcendentals"
  , "flatdyadicmix"
  ]

retiredPaths :: [FilePath]
retiredPaths =
  [ "Exotic/ERL/Exploration/MR15Reachability.agda"
  , "Exotic/ERL/Exploration/OpenESDyadic.agda"
  , "Exotic/ERL/FullCoupled/NoisyNetCoupled.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicBehavior_test.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxFlatDyadicSeparation_test.agda"
  , "Exotic/ERL/FullCoupled/SharedActorCritic.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem.agda"
  , "Exotic/ERL/FullCoupled/SparsemaxActorVsCriticTheorem_test.agda"
  , "Exotic/econlib/RockPaperScissors.agda"
  , "Exotic/econlib/RockPaperScissors_test.agda"
  ]

agdaFiles :: FilePath -> IO [FilePath]
agdaFiles dir = do
  names <- listDirectory dir
  fmap concat $ mapM visit names
  where
    visit name = do
      let path = dir </> name
      isDir <- doesDirectoryExist path
      if isDir
        then if name == ".git" || (dir == ".ci" && name == "external")
             then pure []
             else agdaFiles path
        else pure [path | takeSuffix ".agda" path]

    takeSuffix suffix path = reverse suffix == take (length suffix) (reverse path)

main :: IO ()
main = do
  files <- agdaFiles "."
  problems <- fmap concat $ mapM inspect files
  if null problems
    then putStrLn "forbidden-theorem-families=absent" >> putStrLn "retired-exploration-sources=absent" >> exitSuccess
    else do
      forM_ problems (putStrLn . ("ERROR: " ++))
      exitFailure
  where
    inspect path = do
      source <- readFile path
      let lower = map toLowerAscii source
          tokenErrors = ["forbidden token in " ++ path | any (`isInfixOf` lower) (map (map toLowerAscii) forbidden)]
          retiredErrors = ["retired theorem source present at " ++ path | path `elem` retiredPaths]
      pure (tokenErrors ++ retiredErrors)

    toLowerAscii c
      | c >= 'A' && c <= 'Z' = toEnum (fromEnum c + 32)
      | otherwise = c
