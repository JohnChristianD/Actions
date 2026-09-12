module Main where

import System.Directory (createDirectoryIfMissing)

candidates :: [(String, String)]
candidates =
  [ ("GoodZero", "good-zero", "zero ≡ zero")
  , ("GoodSuccessor", "good-successor", "suc zero ≡ suc zero")
  , ("BadZeroSuccessor", "bad-zero-successor", "zero ≡ suc zero")
  ]

sourceFor :: String -> String -> String
sourceFor moduleName proposition =
  "{-# OPTIONS --safe #-}\n"
  ++ "module " ++ moduleName ++ " where\n\n"
  ++ "open import Agda.Builtin.Equality using (_≡_; refl)\n"
  ++ "open import Agda.Builtin.Nat using (Nat; zero; suc)\n\n"
  ++ "candidate : " ++ proposition ++ "\n"
  ++ "candidate = refl\n"

main :: IO ()
main = do
  let root = ".ci/generated-conjectures"
  createDirectoryIfMissing True root
  mapM_ emit candidates
  where
  emit (moduleName, fileStem, proposition) =
    writeFile
      (root ++ "/" ++ fileStem ++ ".agda")
      (sourceFor moduleName proposition)
  root = ".ci/generated-conjectures"
