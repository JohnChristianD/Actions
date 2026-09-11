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

unless String.contains?(raw, "softsignQIDBDStep"), do: raise("canonical softsign-q-IDBD missing")
unless String.contains?(raw, "softsignQIDBDMetaDecay"), do: raise("canonical meta-decay surface missing")
unless String.contains?(raw, "dyadicEpsilon"), do: raise("canonical dyadic threshold missing from imported core")
unless String.contains?(raw, "canonicalOnlyOptimizer"), do: raise("single global optimizer surface missing")
unless String.contains?(raw, "critic actor transformer representation"), do: raise("four canonical parameter groups missing from imported core")
unless String.contains?(raw, "CanonicalSoftsignSignReLUFFN"), do: raise("canonical three-activation FFN surface missing")
unless String.contains?(raw, "norm : NormPair A"), do: raise("canonical L1/one-path norm pair surface missing")
unless String.contains?(raw, "identityActor"), do: raise("canonical actor identity mode missing from imported core")

IO.puts("v162 canonical source hygiene: PASS")
