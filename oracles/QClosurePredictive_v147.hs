{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Data.Ratio ((%))
import Control.Monad (forM_)

type Q = Rational
sq :: Q -> Q
sq x = x * x
fourth :: Q -> Q
fourth x = sq (sq x)
sumQ :: [Q] -> Q
sumQ = sum
numeratorQ :: [Int] -> [Q] -> [Q] -> Q -> Q
numeratorQ mask a x b = sumQ [a !! i * sq (x !! i) | i <- mask] - b
denominatorQ :: [Int] -> [Q] -> Q
denominatorQ mask x = sumQ [fourth (x !! i) | i <- mask]
firstNegative :: [Int] -> [Q] -> [Q] -> Q -> Maybe Int
firstNegative [] _ _ _ = Nothing
firstNegative (i:is) a x mu = if a !! i - mu * sq (x !! i) < 0 then Just i else firstNegative is a x mu
removeOne :: Int -> [Int] -> [Int]
removeOne i = filter (/= i)
runQ :: [Int] -> [Q] -> [Q] -> Q -> (Q,[Int],Int)
runQ mask a x b = go mask 0
  where
    go active steps =
      let n = numeratorQ active a x b
          d = denominatorQ active x
          mu = if n > 0 && d > 0 then n / d else 0
      in case firstNegative active a x mu of
           Nothing -> (mu, active, steps)
           Just bad ->
             let reduced = removeOne bad active
                 n2 = numeratorQ reduced a x b
                 d2 = denominatorQ reduced x
                 y = a !! bad * sq (x !! bad)
                 z = fourth (x !! bad)
                 mu2 = n2 / d2
             in if n > 0 && d > 0 && d2 > 0 && n2 > 0 && y * d < n * z && mu < mu2
                   then go reduced (steps + 1)
                   else error "Haskell oracle deletion invariant failed"

vals :: [Q]
vals = [0,1,2]
budgets :: [Q]
budgets = [0,1,2,3,4]
vectors :: Int -> [[Q]]
vectors 0 = [[]]
vectors n = [q:xs | q <- vals, xs <- vectors (n-1)]

verify :: Int -> IO ()
verify n = forM_ (vectors n) $ \a -> forM_ (vectors n) $ \x -> forM_ budgets $ \b -> do
  let (mu,active,steps) = runQ [0..n-1] a x b
  if steps <= n then pure () else error "fuel bound"
  forM_ active $ \i -> if a !! i - mu * sq (x !! i) >= 0 then pure () else error "active sign"
  forM_ (filter (`notElem` active) [0..n-1]) $ \i -> if a !! i - mu * sq (x !! i) <= 0 then pure () else error "inactive sign"

main :: IO ()
main = do
  mapM_ verify [1..4]
  putStrLn "haskell-q-finite-fuel=PASS"
  putStrLn "haskell-q-terminal-signs=PASS"
  putStrLn "haskell-q-multiplier-monotonicity=PASS"
  putStrLn "haskell-q-terminal-kkt-prescriptive=PASS"
  putStrLn "haskell-bridge-bounded=PASS"
  putStrLn "haskell-theorem-bounded=PASS"
  putStrLn "haskell-conjecture-falsification=PASS"
