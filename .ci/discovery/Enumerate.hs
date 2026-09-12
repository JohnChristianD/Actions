module Main where

import System.Directory (createDirectoryIfMissing)

header :: String
header = "{-# OPTIONS --safe #-}\n"
  ++ "module GeneratedCandidate where\n\n"
  ++ "open import Agda.Builtin.Equality using (_≡_; refl)\n"
  ++ "open import Agda.Builtin.Nat using (Nat; zero; suc)\n\n"

candidates :: [(String, String)]
candidates =
  [ ("good-zero", header ++ "candidate : zero ≡ zero\ncandidate = refl\n")
  , ("good-successor", header ++ "candidate : suc zero ≡ suc zero\ncandidate = refl\n")
  , ("bad-zero-successor", header ++ "candidate : zero ≡ suc zero\ncandidate = refl\n")
  ]

main :: IO ()
main = do
  let root = ".ci/generated-conjectures"
  createDirectoryIfMissing True root
  mapM_ (emit root) candidates
  where
  emit root (name, source) =
    writeFile (root ++ "/" ++ name ++ ".agda") source
