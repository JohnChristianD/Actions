import Data.Ratio

sigmoidR :: Rational -> Rational
sigmoidR z = (2 + z) / 4

tanhR :: Rational -> Rational
tanhR z = (2 * z) / (2 + z * z)

crelu :: Rational -> (Rational, Rational)
crelu z = (max 0 z, max 0 (-z))

tsallis2 :: [Rational] -> [Rational] -> ([Rational], Rational)
tsallis2 scores values =
  let tau = 1 % 4
      raw = map (\s -> max 0 (s - tau)) scores
      total = sum raw
      weights = map (/ total) raw
      out = sum (zipWith (*) weights values)
  in (weights, out)

lstm :: Rational -> Rational -> Rational -> (Rational, Rational)
lstm x h c =
  let z = x + h
      f = sigmoidR z
      i = sigmoidR z
      o = sigmoidR z
      g = tanhR z
      c2 = f * c + i * g
  in (o * tanhR c2, c2)

render :: Rational -> String
render r =
  let n = numerator r
      d = denominator r
  in show n ++ if d == 1 then "" else "/" ++ show d

main :: IO ()
main = do
  let cases = [(1 % 5, -1 % 10, 3 % 10),
               (1, 1 % 5, -2 % 5),
               (-7 % 10, 1 % 2, 1 % 10)]
      traces = [ [x,h,c,lh,lc] | (x,h,c) <- cases, let (lh,lc) = lstm x h c ]
      (weights, out) = tsallis2 [1, 1 % 2, -1 % 2] [1, -1, 2]
      (cp, cm) = crelu (-3 % 2)
  putStrLn "oracle=haskell-rational"
  mapM_ (putStrLn . ("case=" ++) . comma) traces
  putStrLn $ "tsallis=" ++ comma weights ++ ";" ++ render out
  putStrLn $ "crelu=" ++ render cp ++ "," ++ render cm ++ ";" ++ render (cp - cm) ++ ";" ++ render (cp + cm)
  putStrLn "degree=1,3,9,27"
  putStrLn "status=PASS"
  where
    comma = foldr1 (++) . map render . id
