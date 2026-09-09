import Data.Ratio (Rational, (%), denominator, numerator)
import Data.List (sortBy)

q0 :: Rational
q0 = 0

crelu :: Rational -> (Rational, Rational)
crelu x = (max q0 x, max q0 (-x))

sparsemax :: [Rational] -> ([Rational], Rational)
sparsemax xs = (map (\x -> max q0 (x - tau)) xs, tau)
  where
    u = sortBy (flip compare) xs
    candidates = [ (sum (take k u) - 1) / fromIntegral k | k <- [1 .. length xs] ]
    admissible k t = k == length xs || (u !! k) <= t
    firstK = head [ (k, t) | (k, t) <- zip [1 .. length xs] candidates, admissible k t ]
    tau = snd firstK

rowL1 :: [Rational] -> Rational
rowL1 = sum . map abs

weightL1 :: [[Rational]] -> Rational
weightL1 = sum . map rowL1

path1 :: [[Rational]] -> [[Rational]] -> Rational
path1 w1 w2 = sum
  [ abs (w2 !! o !! h) * rowL1 (w1 !! h)
  | o <- [0 .. length w2 - 1]
  , h <- [0 .. length w1 - 1]
  ]

showR :: Rational -> String
showR q = show (numerator q) ++ "/" ++ show (denominator q)

main :: IO ()
main = do
  let x = (-7) % 3
      (pos, neg) = crelu x
      scores = [5 % 4, 3 % 4, 1 % 2]
      (weights, tau) = sparsemax scores
      w1 = [[1 % 2, (-1) % 3], [1 % 4, 1 % 5]]
      w2 = [[2 % 3, (-3) % 4]]
      l1 = weightL1 w1
      p1 = path1 w1 w2
      degrees = take 5 (iterate (*3) 1)
  if pos - neg /= x then error "CReLU reconstruction failed" else pure ()
  if pos + neg /= abs x then error "CReLU absolute decomposition failed" else pure ()
  if weights /= [3 % 4, 1 % 4, 0] then error "Tsallis-2 weights failed" else pure ()
  if sum weights /= 1 then error "Tsallis-2 normalization failed" else pure ()
  if l1 /= 77 % 60 then error "L1 weight norm failed" else pure ()
  if p1 /= 643 % 720 then error "1-path norm failed" else pure ()
  if degrees /= [1,3,9,27,81] then error "degree recurrence failed" else pure ()
  putStrLn "oracle=haskell-rational"
  putStrLn ("crelu.reconstruct=" ++ showR (pos - neg))
  putStrLn ("crelu.abs=" ++ showR (pos + neg))
  putStrLn ("tsallis.tau=" ++ showR tau)
  putStrLn ("tsallis.weights=" ++ comma weights)
  putStrLn ("weight_l1=" ++ showR l1)
  putStrLn ("path1=" ++ showR p1)
  putStrLn "degree_sequence=1,3,9,27,81"
  putStrLn "status=PASS"
  where
    comma [] = ""
    comma [a] = showR a
    comma (a:as) = showR a ++ "," ++ comma as
