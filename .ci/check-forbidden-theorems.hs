module Main where

import Control.Exception (IOException, try)
import Data.Char (toLower)
import Data.List (isInfixOf, intercalate)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Exit (exitFailure)
import System.FilePath ((</>), splitDirectories)

forbidden :: [String]
forbidden = ["transcendental", "transcendentals", "munchausen", "munchhausen", "münchhausen"]

forbiddenImports :: [String]
forbiddenImports = ["Data.Float", "Data.Rational", "Data.Real", "Complex", "Rational", "Float", "Real", "Transcendental"]

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
    Right text -> do
      let lowered = map toLower text
          theoremErrors = ["forbidden theorem family token present in " ++ path | token <- forbidden, token `isInfixOf` lowered]
          importLines = filter ("open import" `isInfixOf` . map toLower) (lines text)
          importErrors = ["forbidden non-dyadic import in " ++ path ++ ": " ++ line | line <- importLines, token <- forbiddenImports, token `isInfixOf` line]
      pure (theoremErrors ++ importErrors)

main :: IO ()
main = do
  paths <- filter (not . skipPath) <$> walk "."
  errors <- concat <$> mapM checkFile paths
  if null errors
    then putStrLn "flat-dyadic-import-policy=pass"
    else do
      putStrLn (intercalate "\n" (map ("ERROR: " ++) errors))
      exitFailure
