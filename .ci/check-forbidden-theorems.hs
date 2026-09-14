module Main where

import Control.Exception (IOException, try)
import Data.Char (toLower)
import Data.List (isInfixOf, intercalate)
import System.Directory (doesDirectoryExist, listDirectory)
import System.Exit (exitFailure)
import System.FilePath ((</>), splitDirectories, takeExtension)

forbidden :: [String]
forbidden = ["trans" ++ "cendental", "trans" ++ "cendentals", "mun" ++ "chausen", "munch" ++ "hausen", "mün" ++ "chhausen"]

forbiddenImports :: [String]
forbiddenImports = ["Data." ++ "Float", "Data." ++ "Rational", "Data." ++ "Real", "Agda.Builtin.Float", "Complex", "Rational", "Float", "Real", "Trans" ++ "cendental"]

skipPath :: FilePath -> Bool
skipPath path =
  let parts = splitDirectories path
      external = any (== ".ci") parts && any (== "external") parts
  in ".git" `elem` parts || external

walk :: FilePath -> IO [FilePath]
walk root = do
  entries <- listDirectory root
  fmap concat $ mapM descend entries
  where
    descend entry = do
      let path = root </> entry
      if skipPath path
        then pure []
        else do
          directory <- doesDirectoryExist path
          if directory then walk path else pure [path]

isAgdaSource :: FilePath -> Bool
isAgdaSource path = takeExtension path == ".agda"

checkFile :: FilePath -> IO [String]
checkFile path = do
  result <- try (readFile path) :: IO (Either IOException String)
  case result of
    Left _ -> pure []
    Right text -> do
      let lowered = map toLower text
          theoremErrors =
            ["forbidden theorem family token present in " ++ path
            | token <- forbidden
            , token `isInfixOf` lowered]
          importLines =
            filter
              (\line ->
                let l = map toLower line
                in "open import" `isInfixOf` l || "import " `isInfixOf` l)
              (lines text)
          importErrors =
            ["forbidden non-dyadic import in " ++ path ++ ": " ++ line
            | line <- importLines
            , token <- forbiddenImports
            , token `isInfixOf` line]
      pure (theoremErrors ++ importErrors)

main :: IO ()
main = do
  paths <- filter (\path -> not (skipPath path) && isAgdaSource path) <$> walk "."
  errors <- concat <$> mapM checkFile paths
  if null errors
    then putStrLn "flat-dyadic-import-policy=pass"
    else do
      putStrLn (intercalate "\n" (map ("ERROR: " ++) errors))
      exitFailure
