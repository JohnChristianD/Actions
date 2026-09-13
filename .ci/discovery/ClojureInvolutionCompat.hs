module Main where

import Data.List (isInfixOf)
import System.Exit (exitFailure, exitSuccess)

validIndex :: Int -> Int -> Bool
validIndex n i = n > 0 && i >= 0 && i < n

adjacentSwap :: Int -> Int -> Either String ([Int] -> [Int])
adjacentSwap n i
  | not (validIndex n i) || i + 1 >= n = Left "adjacent-swap index out of range"
  | otherwise = Right $ \v ->
      let j = i + 1
          vi = at v i
          vj = at v j
      in replace j vi (replace i vj v)

signFlip :: Int -> Int -> Either String ([Int] -> [Int])
signFlip n i
  | not (validIndex n i) = Left "sign-flip index out of range"
  | otherwise = Right $ \v -> replace i (negate (at v i)) v

at :: [a] -> Int -> a
at xs i = xs !! i

replace :: Int -> a -> [a] -> [a]
replace i x xs = take i xs ++ [x] ++ drop (i + 1) xs

composeLocal :: [[Int] -> [Int]] -> [Int] -> [Int]
composeLocal operations v = foldl (flip ($)) v operations

involution :: ([Int] -> [Int]) -> [[Int]] -> Bool
involution operation domain =
  all (\v -> v == operation (operation v)) domain

sucImport :: String
sucImport = "open import Agda.Builtin.Nat using (Nat; zero; suc)"

selectSafeRule :: String -> String -> String
selectSafeRule agdaLog source
  | "Not in scope: suc" `isInfixOf` agdaLog && not (sucImport `isInfixOf` source) = "add-suc-import"
  | otherwise = "none"

insertAfterModule :: String -> String -> String
insertAfterModule source extra =
  case break ("module " `isPrefixOf`) (lines source) of
    (before, []) -> source
    (before, moduleLine : after) -> unlines (before ++ [moduleLine, extra] ++ after)
  where
    isPrefixOf prefix text = take (length prefix) text == prefix

applySafeRule :: String -> String -> String
applySafeRule "add-suc-import" source
  | sucImport `isInfixOf` source = source
  | otherwise = insertAfterModule source sucImport
applySafeRule _ source = source

check :: Bool
check =
  case (adjacentSwap 4 0, signFlip 4 3) of
    (Right swap, Right flip) ->
      let basis = composeLocal [swap, flip]
          domain = [[0,1,2,3], [3,2,1,0], [-1,4,2,8]]
          swapOk = involution swap domain
          flipOk = involution flip domain
          basisOk = involution basis domain
          logText = "Not in scope: suc\n"
          source = "module Demo where\nopen import Agda.Builtin.Nat\n"
          selected = selectSafeRule logText source == "add-suc-import"
          noneSelected = selectSafeRule "unrecognised error\n" "module Demo where\n" == "none"
          once = applySafeRule "add-suc-import" source
          twice = applySafeRule "add-suc-import" once
          idempotent = once == twice
      in and [swapOk, flipOk, basisOk, selected, noneSelected, idempotent]
    _ -> False

main :: IO ()
main = if check then exitSuccess else exitFailure
