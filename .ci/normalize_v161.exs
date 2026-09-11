manifest = ".ci/canonical-module.txt"
source = File.read!(manifest) |> String.split("\n") |> Enum.at(0) |> String.trim()
raw = File.read!(source) |> String.replace("\r\n", "\n")
module = source |> Path.rootname() |> String.replace("/", ".")
expected = "{-# OPTIONS --safe #-}\nmodule #{module} where"
unless String.starts_with?(raw, expected), do: raise("canonical source header/module mismatch: #{source}")

forbidden = [
  "StoSignSGD",
  "StoSignSGDv2",
  "Munchausen",
  "munchausen",
  "Lion",
  "lion",
  "Adam",
  "AdaMax",
  "RAdam",
  "beta1",
  "beta2",
  "LayerNorm",
  "BatchNorm",
  "BatchRenorm",
  "Newton",
  "DiagonalNewton",
  "NewtonRaphson",
  "Certificate",
  "postulate",
  "{!!}",
  "CReLU",
  "SmoothAlgebra.exp",
  "SmoothAlgebra.log",
  "clamp",
  "squash"
]

matches = Enum.filter(forbidden, &String.contains?(raw, &1))
if matches != [], do: raise("forbidden retired formulation(s) remain in #{source}: #{Enum.join(matches, ", ")}")

required = [
  "F4IntSigmaDeltaState",
  "f4ExactEMA",
  "f4MomentumSigmaDeltaLaw",
  "f4LogSigmaDeltaLaw",
  "canonicalOptimizerIsF4IntSigmaDelta",
  "CanonicalSoftsignSignReLUFFN",
  "NormPair",
  "FullFiniteOrderedRationalLearner"
]

missing = Enum.reject(required, &String.contains?(raw, &1))
if missing != [], do: raise("canonical source missing: #{Enum.join(missing, ", ")}")

IO.puts("canonical source hygiene: PASS #{source}")
