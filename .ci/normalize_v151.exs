path = "Exotic/ERL/FullCoupled/EfficientCHAD_StoSignSGDv2_Tsallis2_v151.agda"
text = File.read!(path) |> String.replace("\r\n", "\n")

forbidden = [
  "LayerNorm",
  "BatchNorm",
  "BatchRenorm",
  "CReLUCertificate",
  "noMomentum",
  "beta1Zero",
  "python3",
]

Enum.each(forbidden, fn token ->
  if String.contains?(text, token) do
    raise "forbidden v151 token remains: #{token}"
  end
end)

required = [
  "sign-q-IDBD",
  "Tsallis2",
  "onePathNorm",
  "weightL1",
  "beta1Numerator",
  "beta1Exponent",
  "metaStepExponent",
  "Munchausen",
  "overestimation",
  "CVT",
  "OpenES",
]

Enum.each(required, fn token ->
  unless String.contains?(text, token) do
    raise "required v151 token missing: #{token}"
  end
end)

File.write!(path, text)
IO.puts("v151 Elixir normalisation/hygiene: PASS")
