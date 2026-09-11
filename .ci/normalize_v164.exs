manifest = ".ci/canonical-module.txt"
source = File.read!(manifest) |> String.split("\n") |> Enum.at(0) |> String.trim()
raw = File.read!(source) |> String.replace("\r\n", "\n")
module = source |> Path.rootname() |> String.replace("/", ".")
expected = "{-# OPTIONS --safe #-}\nmodule #{module} where"
unless String.starts_with?(raw, expected), do: raise("canonical source header/module mismatch")

forbidden = [
  "StoSignSGD", "StoSignSGDv2", "Munchausen", "munchausen", "Lion", "lion",
  "Adam", "AdaMax", "RAdam", "beta1", "LayerNorm", "BatchNorm", "BatchRenorm",
  "Newton", "DiagonalNewton", "NewtonRaphson", "Certificate", "postulate", "{!!}",
  "CReLU", "SmoothAlgebra.exp", "SmoothAlgebra.log", "clamp", "squash"
]

matches = Enum.filter(forbidden, &String.contains?(raw, &1))
if matches != [], do: raise("forbidden retired formulation(s) remain in #{source}: #{Enum.join(matches, ", ")}")

required = [
  "F4IntSigmaDeltaConfig", "F4IntSigmaDeltaState", "SigmaDeltaMomentumQuantizer",
  "SigmaDeltaLogQuantizer", "beta2", "half : R", "fullEffectiveState", "fullPrequantizedState",
  "f4IntSigmaDeltaStep", "f4IntSigmaDeltaMomentumReconstruction",
  "f4IntSigmaDeltaIntegratorLaw", "canonicalOnlyOptimizer", "NormPair",
  "CanonicalSoftsignSignReLUFFN", "canonicalLearnerUpdate", "pow2Int", "intEmbed"
]

missing = Enum.reject(required, &String.contains?(raw, &1))
if missing != [], do: raise("canonical source missing: #{Enum.join(missing, ", ")}")

optimizer_state_count = Enum.count(["eQ", "rE", "rL", "logStep"], &String.contains?(raw, &1))
unless optimizer_state_count == 4, do: raise("F4-Int Sigma-Delta optimizer state surface incomplete")

IO.puts("canonical F4-Int Sigma-Delta source hygiene: PASS #{source}")
