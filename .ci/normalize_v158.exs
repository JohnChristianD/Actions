path = "Exotic/ERL/FullCoupled/EfficientCHAD_v158.agda"
text = File.read!(path) |> String.replace("\r\n", "\n")

forbidden = ["StoSignSGDv2", "StoSignSGD", "LayerNorm", "BatchNorm", "BatchRenorm", "Newton", "Certificate", "postulate", "{!!}", "CReLU"]
required = ["--safe", "SignReLU", "signQIDBDDirection", "LionFeatureState", "qLog2", "munchausenAlphaQLog2", "Tsallis2State", "hStepCEMMaxTarget", "TrueOnlineTrace", "weightL1", "onePathNorm", "algorithm11L2RoundedDyad", "RepresentationOnlyState", "CVTCell", "OpenESEmitter", "proximalSignLaw", "clarkeBranchLaw", "medianL1Law", "tropicalMaxLaw"]

Enum.each(forbidden, fn token ->
  if String.contains?(text, token), do: raise("forbidden v158 token remains: #{token}")
end)
Enum.each(required, fn token ->
  unless String.contains?(text, token), do: raise("required v158 token missing: #{token}")
end)

File.write!(path, text)
IO.puts("v158 Elixir canonical normalization/hygiene: PASS")
