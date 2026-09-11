path = "Exotic/ERL/FullCoupled/EfficientCHAD_v157.agda"
text = File.read!(path) |> String.replace("\r\n", "\n")
required = ["module Exotic.ERL.FullCoupled.EfficientCHAD_v157", "record SignReLU", "stackComposition", "hStepComposition", "hStepTrueOnlineLaw", "record SignQIDBD", "record Lion", "algorithm11L2NearestDyad", "record VEBFitness", "record RepresentationCandidate", "proximalGeometry", "clarkeGeometryLaw", "medianQuantileGeometry", "tropicalGeometry"]
Enum.each(required, fn token -> unless String.contains?(text, token), do: raise "required v157 token missing: #{token}" end)
forbidden = ["StoSignSGDv2", "StoSignSGD", "LayerNorm", "BatchNorm", "BatchRenorm", "DiagonalNewton", "NewtonRaphson", "Certificate", "setup-python", "ruby/setup-ruby", "python3"]
Enum.each(forbidden, fn token -> if String.contains?(text, token), do: raise "forbidden v157 token present: #{token}" end)
File.write!(path, text)
IO.puts("v157-elixir-normalization=PASS")
