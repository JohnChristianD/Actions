import Data.Ratio ((%), numerator, denominator)

sigmoidR :: Rational -> Rational
sigmoidR z = (2 + z) / 4

tanhR :: Rational -> Rational
tanhR z = (2 * z) / (2 + z * z)

lstm :: Rational -> Rational -> Rational -> (Rational, Rational)
lstm x h c =
  let z = x + h
      f = sigmoidR z
      i = sigmoidR z
      o = sigmoidR z
      g = tanhR z
      c2 = f * c + i * g
      h2 = o * tanhR c2
  in (h2, c2)

q :: Integer -> Integer -> Rational
q = (%)

cases :: [(Rational, Rational, Rational)]
cases = [(q 1 5, q (-1) 10, q 3 10),
         (q 1 1, q 1 5, q (-2) 5),
         (q (-7) 10, q 1 2, q 1 10)]

render :: Rational -> String
render r =
  let n = numerator r
      d = denominator r
  in show n ++ if d == 1 then "" else "/" ++ show d

main :: IO ()
main = mapM_ emit cases
  where
    emit (x,h,c) = let (lh,lc) = lstm x h c
                   in putStrLn $ render x ++ "," ++ render h ++ "," ++ render c ++ "," ++ render lh ++ "," ++ render lc
