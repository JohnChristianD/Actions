path = "Exotic/ERL/FullCoupled/EfficientCHAD_v155.agda"
text = File.read!(path) |> String.replace("\r\n", "\n")

required = [
  "module Exotic.ERL.FullCoupled.EfficientCHAD_v155",
  "record SignReLU",
  "record RepresentationLayer",
  "stackComposition",
  "tsallis2MunchausenBonus",
  "hStepReturnComposition",
  "hStepTrueOnlineCompatible",
  "record SignQIDBDState",
  "record LionState",
  "algorithm11L2NearestDyad",
  "record VEBFitness",
  "record RepresentationCandidate",
  "proximalGeometry",
  "clarkeGeometryLaw",
  "medianQuantileGeometry",
  "tropicalComposition"
]

for token <- required do
  unless String.contains?(text, token), do: raise "required v155 token missing: #{token}"
end

forbidden = [
  "StoSignSGDv2",
  "StoSignSGD",
  "LayerNorm",
  "BatchNorm",
  "BatchRenorm",
  "DiagonalNewton",
  "NewtonRaphson",
  "Certificate",
  "setup-python",
  "ruby/setup-ruby",
  "python3"
]

for token <- forbidden do
  if String.contains?(text, token), do: raise "forbidden v155 token present: #{token}"
end

File.write!(path, text)
IO.puts("v155-elixir-normalization=PASS")
