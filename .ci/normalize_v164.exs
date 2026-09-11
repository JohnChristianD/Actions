source = "Exotic/ERL/FullCoupled/EfficientCHAD_v164.agda"
raw = File.read!(source) |> String.replace("\r\n", "\n")
expected = "{-# OPTIONS --safe #-}\nmodule Exotic.ERL.FullCoupled.EfficientCHAD_v164 where"
unless String.starts_with?(raw, expected), do: raise("v164 source header/module mismatch")

forbidden = [
  "StoSignSGD", "StoSignSGDv2", "Munchausen", "munchausen", "Lion", "lion",
  "Adam", "AdaMax", "RAdam", "beta1", "LayerNorm", "BatchNorm", "BatchRenorm",
  "Newton", "DiagonalNewton", "NewtonRaphson", "Certificate", "postulate", "{!!}",
  "CReLU", "SmoothAlgebra.exp", "SmoothAlgebra.log", "clamp", "squash", "momentum"
]

matches = Enum.filter(forbidden, &String.contains?(raw, &1))
if matches != [], do: raise("forbidden retired formulation(s) remain in v164: #{Enum.join(matches, ", ")}")

required = [
  "F4IntSigmaDeltaConfig", "F4IntSigmaDeltaState", "SigmaDeltaMomentumQuantizer",
  "SigmaDeltaLogQuantizer", "beta2", "half : R", "fullEffectiveState", "fullPrequantizedState",
  "f4IntSigmaDeltaStep", "f4IntSigmaDeltaMomentumReconstruction",
  "f4IntSigmaDeltaIntegratorLaw", "canonicalOnlyOptimizer", "NormPair",
  "CanonicalSoftsignSignReLUFFN", "canonicalLearnerUpdate", "pow2Int", "intEmbed"
]

missing = Enum.reject(required, &String.contains?(raw, &1))
if missing != [], do: raise("canonical v164 surface missing: #{Enum.join(missing, ", ")}")

IO.puts("v164 canonical source hygiene: PASS")
