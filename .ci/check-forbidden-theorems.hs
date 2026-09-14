module Main where

import Control.Exception (IOException, try)
import Data.Char (toLower)
import Data.List (isInfixOf, intercalate)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Exit (exitFailure)
import System.FilePath ((</>), splitDirectories)

forbidden :: [String]
forbidden = ["transcendental", "transcendentals", "munchausen", "munchhausen", "münchhausen"]

skipPath :: FilePath -> Bool
skipPath path = any (`elem` splitDirectories path) [".git", ".ci" </> "external"]

walk :: FilePath -> IO [FilePath]
walk root = do
  entries <- listDirectory root
  fmap concat $ mapM descend entries
  where
    descend entry = do
      let path = root </> entry
      directory <- doesDirectoryExist path
      if directory then walk path else pure [path]

checkFile :: FilePath -> IO [String]
checkFile path = do
  result <- try (readFile path) :: IO (Either IOException String)
  case result of
    Left _ -> pure []
    Right text ->
      let lowered = map toLower text
      in pure ["forbidden theorem family token present in " ++ path | token <- forbidden, token `isInfixOf` lowered]

main :: IO ()
main = do
  paths <- filter (not . skipPath) <$> walk "."
  errors <- concat <$> mapM checkFile paths
  if null errors
    then putStrLn "forbidden-theorem-families=absent"
    else do
      putStrLn (intercalate "\n" (map ("ERROR: " ++) errors))
      exitFailure
