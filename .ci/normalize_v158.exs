path = "Exotic/ERL/FullCoupled/EfficientCHAD_v158.agda"
text = File.read!(path) |> String.replace("\r\n", "\n")

text = String.replace(text,
  "_≠_ : ∀ {A : Set} → A → A → Set\nx ≠ y = x ≡ y → Set",
  "data Bottom : Set where\n\n_≠_ : ∀ {A : Set} → A → A → Set\nx ≠ y = x ≡ y → Bottom")
text = String.replace(text,
  "hStepReturn (r ∷ []) gamma bootstrap ≡ r + gamma * bootstrap",
  "hStepReturn (r ∷ []) gamma bootstrap ≡ r + (gamma * bootstrap)")

bodyRepairs = [
  {"r + gamma * hStepReturn rs gamma bootstrap", "r + (gamma * hStepReturn rs gamma bootstrap)"},
  {"b * m + c * x", "(b * m) + (c * x)"},
  {"TrueOnlineTrace.alpha s * decay * featureDot", "(TrueOnlineTrace.alpha s * decay) * featureDot"},
  {"neg A", "neg _"},
  {"sign A", "sign _"},
  {"abs A", "abs _"},
  {"max A", "max _"},
  {"zero A", "zero _"},
  {"one A", "one _"},
  {"recip A", "recip _"},
  {"addNegR A", "addNegR _"},
  {"signIdempotent A", "signIdempotent _"},
  {"absIdempotent A", "absIdempotent _"},
  {"maxLeLeft A", "maxLeLeft _"},
  {"maxLeRight A", "maxLeRight _"},
  {"addAssoc A", "addAssoc _"},
  {"addComm A", "addComm _"},
  {"addZeroR A", "addZeroR _"},
  {"mulAssoc A", "mulAssoc _"},
  {"mulComm A", "mulComm _"},
  {"mulOneR A", "mulOneR _"},
  {"distrib A", "distrib _"},
  {"zeroMulR A", "zeroMulR _"},
  {"recipLaw A", "recipLaw _"},
  {"_*_ A", "_*_ _"},
  {"_+_ A", "_+_ _"}
]

text = text
  |> String.split("\n")
  |> Enum.map(fn line ->
    if String.contains?(line, "=") do
      Enum.reduce(bodyRepairs, line, fn {from, to}, acc -> String.replace(acc, from, to) end)
    else
      line
    end
  end)
  |> Enum.join("\n")

forbidden = ["StoSignSGDv2", "StoSignSGD", "LayerNorm", "BatchNorm", "BatchRenorm", "Newton", "Certificate", "postulate", "{!!}", "CReLU"]
required = ["--safe", "SignReLU", "signQIDBDDirection", "LionFeatureState", "qLog2", "munchausenAlphaQLog2", "Tsallis2State", "hStepCEMMaxTarget", "TrueOnlineTrace", "weightL1", "onePathNorm", "algorithm11L2RoundedDyad", "RepresentationOnlyState", "CVTCell", "OpenESEmitter", "proximalSignLaw", "clarkeBranchLaw", "medianL1Law", "tropicalMaxLaw"]
Enum.each(forbidden, fn token -> if String.contains?(text, token), do: raise("forbidden v158 token remains: #{token}") end)
Enum.each(required, fn token -> unless String.contains?(text, token), do: raise("required v158 token missing: #{token}") end)
File.write!(path, text)
IO.puts("v158 Elixir canonical normalization/hygiene: PASS")
