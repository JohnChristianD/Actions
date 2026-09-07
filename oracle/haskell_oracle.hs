import Text.Printf (printf)

sigmoid :: Double -> Double
sigmoid z = 1.0 / (1.0 + exp (-z))

tanh' :: Double -> Double
tanh' z = tanh z

lstmStep :: Double -> Double -> Double -> Double
lstmStep x h c =
  let f = sigmoid (0.7 * x + 0.4 * h)
      i = sigmoid (0.3 * x - 0.2 * h)
      o = sigmoid (-0.1 * x + 0.5 * h)
      g = tanh' (0.6 * x + 0.1 * h)
      c' = f * c + i * g
      h' = o * tanh' c'
  in h'

main :: IO ()
main = do
  putStrLn "x,h,c,output"
  putStrLn "0.2,-0.1,0.3,"
  printf "%0.17g,%0.17g,%0.17g,%0.17g\n" (0.2::Double) (-0.1::Double) (0.3::Double) (lstmStep 0.2 (-0.1) 0.3)
  printf "%0.17g,%0.17g,%0.17g,%0.17g\n" (1.0::Double) 0.2 (-0.4::Double) (lstmStep 1.0 0.2 (-0.4))
  printf "%0.17g,%0.17g,%0.17g,%0.17g\n" (-0.7::Double) 0.5 0.1 (lstmStep (-0.7) 0.5 0.1)
