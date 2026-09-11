source = "Exotic/ERL/FullCoupled/EfficientCHAD_v162.agda"
raw = File.read!(source) |> String.replace("\r\n", "\n")
expected = "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.FullCoupled.EfficientCHAD_v162 where"
unless String.starts_with?(raw, expected), do: raise("v162 source header/module mismatch")

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
  "squash",
  "momentum"
]

matches = Enum.filter(forbidden, &String.contains?(raw, &1))
if matches != [], do: raise("forbidden retired formulation(s) remain in v162: #{Enum.join(matches, ", ")}")

required = [
  "softsignQIDBDStep",
  "SoftsignQIDBDMetaDecay",
  "canonicalOnlyOptimizer",
  "CanonicalSoftsignSignReLUFFN",
  "canonicalNormPairSurface",
  "canonicalLearnerUpdate"
]

missing = Enum.reject(required, &String.contains?(raw, &1))
if missing != [], do: raise("canonical v162 surface missing: #{Enum.join(missing, ", ")}")

IO.puts("v162 canonical source hygiene: PASS")
