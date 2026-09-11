source = "Exotic/ERL/FullCoupled/EfficientCHAD_v163.agda"
raw = File.read!(source) |> String.replace("\r\n", "\n")
expected = "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.FullCoupled.EfficientCHAD_v163 where"
unless String.starts_with?(raw, expected), do: raise("v163 source header/module mismatch")

forbidden = [
  "StoSignSGD", "StoSignSGDv2", "Munchausen", "munchausen", "Lion", "lion",
  "Adam", "AdaMax", "RAdam", "beta1", "beta2", "LayerNorm", "BatchNorm",
  "BatchRenorm", "Newton", "DiagonalNewton", "NewtonRaphson", "Certificate",
  "postulate", "{!!}", "CReLU", "SmoothAlgebra.exp", "SmoothAlgebra.log",
  "clamp", "squash", "momentum"
]

matches = Enum.filter(forbidden, &String.contains?(raw, &1))
if matches != [], do: raise("forbidden retired formulation(s) remain in v163: #{Enum.join(matches, ", ")}")

required = [
  "softsignQIDBDStep", "SoftsignQIDBDMetaDecay", "canonicalOnlyOptimizer",
  "CanonicalSoftsignSignReLUFFN", "NormPair", "canonicalLearnerUpdate",
  "idbdPow2", "idbdLog2", "hStepReturn"
]

missing = Enum.reject(required, &String.contains?(raw, &1))
if missing != [], do: raise("canonical v163 surface missing: #{Enum.join(missing, ", ")}")

IO.puts("v163 canonical source hygiene: PASS")
