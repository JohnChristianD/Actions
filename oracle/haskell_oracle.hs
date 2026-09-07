import Text.Printf (printf)

sigmoid :: Double -> Double
sigmoid z = 1.0 / (1.0 + exp (-z))

lstmStep :: Double -> Double -> Double -> Double
lstmStep x h c =
  let f = sigmoid (0.7 * x + 0.4 * h)
      i = sigmoid (0.3 * x - 0.2 * h)
      o = sigmoid (-0.1 * x + 0.5 * h)
      g = tanh (0.6 * x + 0.1 * h)
      c' = f * c + i * g
  in o * tanh c'

emit :: Double -> Double -> Double -> IO ()
emit x h c = printf "%.17f,%.17f,%.17f,%.17f\n" x h c (lstmStep x h c)

main :: IO ()
main = do
  putStrLn "x,h,c,output"
  emit 0.2 (-0.1) 0.3
  emit 1.0 0.2 (-0.4)
  emit (-0.7) 0.5 0.1
