module Main where

import Control.Monad (forM_)
import Data.List (isInfixOf)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Exit (exitFailure, exitSuccess)
import System.FilePath ((</>))

forbidden :: [String]
forbidden =
  [ "transcendental"
  , "transcendentals"
  , "flatdyadicmix"
  ]

agdaFiles :: FilePath -> IO [FilePath]
agdaFiles dir = do
  names <- listDirectory dir
  fmap concat (mapM visit names)
  where
  visit name = do
    let path = dir </> name
    if name == ".git" || (dir == ".ci" && name == "external")
      then pure []
      else do
        isDir <- doesDirectoryExist path
        if isDir then agdaFiles path else pure [path | ".agda" `isSuffixOf` path]

  isSuffixOf suffix path = reverse suffix == take (length suffix) (reverse path)

main :: IO ()
main = do
  files <- agdaFiles "."
  problems <- fmap concat (mapM inspect files)
  if null problems
    then putStrLn "forbidden-theorem-families=absent" >> exitSuccess
    else do
      forM_ problems (putStrLn . ("ERROR: " ++))
      exitFailure
  where
  inspect path = do
    source <- readFile path
    let lower = map lowerAscii source
    pure ["forbidden token in " ++ path | any (`isInfixOf` lower) (map (map lowerAscii) forbidden)]

  lowerAscii c
    | c >= 'A' && c <= 'Z' = toEnum (fromEnum c + 32)
    | otherwise = c
