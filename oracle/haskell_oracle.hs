import Text.Printf (printf)

sigmoid :: Double -> Double
sigmoid z = 1 / (1 + exp (-z))

lstm :: Double -> Double -> Double -> (Double, Double)
lstm x h c =
  let z = x + h
      f = sigmoid z
      i = sigmoid z
      o = sigmoid z
      g = tanh z
      c2 = f * c + i * g
      h2 = o * tanh c2
  in (h2, c2)

main :: IO ()
main = mapM_ emit [(0.2,-0.1,0.3),(1.0,0.2,-0.4),(-0.7,0.5,0.1)]
  where
    emit (x,h,c) = let (lh,lc) = lstm x h c
                    in printf "%.12f,%.12f,%.12f,%.12f\n" x h c lh lc
