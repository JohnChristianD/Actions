import Text.Printf (printf)

sig :: Double -> Double
sig z = 1 / (1 + exp (-z))

tanh' :: Double -> Double
tanh' = tanh

lstm :: Double -> Double -> Double -> (Double, Double)
lstm x h c = (h2, c2)
  where
    z = x + h
    f = sig z; i = sig z; o = sig z; g = tanh' z
    c2 = f * c + i * g
    h2 = o * tanh' c2

gru :: Double -> Double -> Double
gru x h = (1 - z) * n + z * h
  where
    z = sig (x + h)
    r = sig (x + h)
    n = tanh' (x + r * h)

main :: IO ()
main = mapM_ emit [(0.2,-0.1,0.3),(1.0,0.2,-0.4),(-0.7,0.5,0.1)]
  where
    emit (x,h,c) = let (lh,lc) = lstm x h c; gh = gru x h
                    in printf "%.10f,%.10f,%.10f,%.10f,%.10f,%.10f\n" x h c lh lc gh
